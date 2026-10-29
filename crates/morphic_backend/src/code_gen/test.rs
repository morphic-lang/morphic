use id_collections::IdVec;
use morphic_common::config::LlvmConfig;
use morphic_common::data::first_order_ast::FuncSymbols;
use morphic_common::data::intrinsics::Intrinsic;
use morphic_common::data::low_ast::*;
use morphic_common::data::metadata::Metadata;
use morphic_common::data::mode_annot_ast::Mode;
use morphic_common::data::num_type::{IntType, NumLit, NumType};
use morphic_common::data::rc_specialized_ast::{CustomTypes, ModeScheme};
use morphic_common::data::tail_rec_ast::TailFuncSymbols;
use morphic_common::pseudoprocess::{ExitStatus, Stdio};
use std::io::Read;

struct ProgramBuilder {
    bindings: Vec<(Type, Expr, Metadata)>,
}

impl ProgramBuilder {
    fn new() -> Self {
        Self { bindings: vec![] }
    }

    fn add_binding(&mut self, type_: Type, expr: Expr) -> LocalId {
        self.bindings.push((type_, expr, Metadata::default()));
        // 0 is reserved for function arguments, so we start at 1
        LocalId(self.bindings.len())
    }

    fn type_of(&self, local: LocalId) -> &Type {
        &self.bindings[local.0 - 1].0
    }

    fn finish(mut self) -> Program {
        let result = self.add_binding(Type::Tuple(vec![]), Expr::Tuple(vec![]));
        let body = Expr::LetMany(self.bindings, result);

        let func = FuncDef {
            tail_funcs: IdVec::new(),
            tail_func_symbols: IdVec::new(),
            arg_type: Type::Tuple(vec![]),
            ret_type: Type::Tuple(vec![]),
            body,
            profile_point: None,
        };

        let mut funcs = IdVec::new();
        let _ = funcs.push(func);

        let mut func_symbols = IdVec::new();
        let _ = func_symbols.push(TailFuncSymbols::Acyclic(FuncSymbols::MainWrapper));

        Program {
            mod_symbols: IdVec::new(),
            custom_types: CustomTypes {
                types: IdVec::new(),
            },
            custom_type_symbols: IdVec::new(),
            funcs,
            func_symbols,
            schemes: IdVec::new(),
            profile_points: IdVec::new(),
            main: CustomFuncId(0),
        }
    }

    fn build_output(&mut self, s: LocalId) {
        self.add_binding(
            Type::Tuple(vec![]),
            Expr::IoOp(IoOp::Output(
                ModeScheme::Array(Mode::Borrowed, Box::new(ModeScheme::Num(NumType::U8))),
                s,
            )),
        );
    }

    fn build_byte_array(&mut self) -> LocalId {
        self.add_binding(
            Type::Array(Box::new(Type::Num(NumType::U8))),
            Expr::ArrayOp(
                ModeScheme::Array(Mode::Owned, Box::new(ModeScheme::Num(NumType::U8))),
                ArrayOp::New,
            ),
        )
    }

    fn build_push_byte(&mut self, arr: LocalId, byte: LocalId) -> LocalId {
        self.add_binding(
            Type::Array(Box::new(Type::Num(NumType::U8))),
            Expr::ArrayOp(
                ModeScheme::Array(Mode::Owned, Box::new(ModeScheme::Num(NumType::U8))),
                ArrayOp::Push(arr, byte),
            ),
        )
    }

    fn build_string_lit(&mut self, s: &str) -> LocalId {
        let mut arr = self.build_byte_array();
        for c in s.as_bytes() {
            let c_bound = self.build_num_lit(NumLit::U8(*c));
            arr = self.build_push_byte(arr, c_bound);
        }
        arr
    }

    fn build_num_lit(&mut self, lit: NumLit) -> LocalId {
        self.add_binding(Type::Num(lit.num_type()), Expr::NumLit(lit))
    }

    fn build_tuple(&mut self, items: &[LocalId]) -> LocalId {
        let types = items
            .iter()
            .map(|&item| self.type_of(item).clone())
            .collect();
        self.add_binding(Type::Tuple(types), Expr::Tuple(items.to_vec()))
    }

    /// Applies an intrinsic whose result is a number of the type.
    fn build_num_op(&mut self, intr: Intrinsic, ret: NumType, arg: LocalId) -> LocalId {
        self.add_binding(Type::Num(ret), Expr::Intrinsic(intr, arg))
    }

    /// Applies a binary intrinsic whose result is a number of the type.
    fn build_num_binop(
        &mut self,
        intr: Intrinsic,
        ret: NumType,
        lhs: LocalId,
        rhs: LocalId,
    ) -> LocalId {
        let args = self.build_tuple(&[lhs, rhs]);
        self.build_num_op(intr, ret, args)
    }

    /// Converts a number to a `U8`, which keeps an integer's low bits.
    fn build_to_u8(&mut self, num: LocalId) -> LocalId {
        let &Type::Num(from) = self.type_of(num) else {
            panic!("expected a number");
        };
        if from == NumType::U8 {
            num
        } else {
            self.build_num_op(Intrinsic::Convert(from, NumType::U8), NumType::U8, num)
        }
    }
}

/// Compiles and runs the program, and returns its output.
fn run_for_output(prog: Program) -> Vec<u8> {
    let mut child = super::run(Stdio::Piped, prog, &LlvmConfig::default(), None).unwrap();
    let mut output = Vec::new();
    child
        .stdout
        .take()
        .unwrap()
        .read_to_end(&mut output)
        .unwrap();
    assert_eq!(child.wait().unwrap(), ExitStatus::Success);
    output
}

#[test]
fn test_print_hello() {
    let mut builder = ProgramBuilder::new();
    let s = builder.build_string_lit("Hello, world!");
    builder.build_output(s);

    let prog = builder.finish();
    let _child = super::run(Stdio::Piped, prog, &LlvmConfig::default(), None).unwrap();
}

/// Runs intrinsics at every integer width and signedness, and checks their results.  Each case
/// pushes its result as a `U8` onto an array the program outputs; the operands are chosen so that
/// the wrong signedness, width, or saturation would give a different byte.
#[test]
fn test_num_intrinsics() {
    use Intrinsic::*;
    use NumType::*;

    let mut b = ProgramBuilder::new();
    let mut arr = b.build_byte_array();
    let mut expected = Vec::new();
    let mut check = |b: &mut ProgramBuilder, value: LocalId, byte: u8| {
        let value = b.build_to_u8(value);
        arr = b.build_push_byte(arr, value);
        expected.push(byte);
    };

    // Bit counts.
    let x = b.build_num_lit(NumLit::I16(0x7FFF));
    let v = b.build_num_op(Ctpop(IntType::I16), I16, x);
    check(&mut b, v, 15);
    let x = b.build_num_lit(NumLit::U32(1));
    let v = b.build_num_op(Ctlz(IntType::U32), U32, x);
    check(&mut b, v, 31);
    let x = b.build_num_lit(NumLit::I8(0));
    let v = b.build_num_op(Cttz(IntType::I8), I8, x);
    check(&mut b, v, 8);

    // Float to integer saturates at the integer's range and takes NaN to zero.
    let x = b.build_num_lit(NumLit::F32(1000.0));
    let v = b.build_num_op(Convert(F32, I8), I8, x);
    check(&mut b, v, 127);
    let v = b.build_num_op(Convert(F32, U8), U8, x);
    check(&mut b, v, 255);
    let x = b.build_num_lit(NumLit::F64(-5.0));
    let v = b.build_num_op(Convert(F64, I16), I16, x);
    check(&mut b, v, 251);
    let v = b.build_num_op(Convert(F64, U16), U16, x);
    check(&mut b, v, 0);
    let x = b.build_num_lit(NumLit::F64(-129.0));
    let v = b.build_num_op(Convert(F64, I32), I32, x);
    check(&mut b, v, 127);
    let v = b.build_num_op(Convert(F64, U32), U32, x);
    check(&mut b, v, 0);
    let x = b.build_num_lit(NumLit::F64(-2.0));
    let v = b.build_num_op(Convert(F64, I64), I64, x);
    check(&mut b, v, 254);
    let v = b.build_num_op(Convert(F64, U64), U64, x);
    check(&mut b, v, 0);
    let x = b.build_num_lit(NumLit::F64(f64::NAN));
    let v = b.build_num_op(Convert(F64, I64), I64, x);
    check(&mut b, v, 0);

    // Integer to float extends by the source's signedness.
    let x = b.build_num_lit(NumLit::U8(200));
    let v = b.build_num_op(Convert(U8, F32), F32, x);
    check(&mut b, v, 200);
    let x = b.build_num_lit(NumLit::U64(u64::MAX));
    let v = b.build_num_op(Convert(U64, F64), F64, x);
    check(&mut b, v, 255);

    // Converting between integers of one width keeps the bits.
    let x = b.build_num_lit(NumLit::I8(-1));
    let v = b.build_num_op(Convert(I8, U8), U8, x);
    check(&mut b, v, 255);
    let x = b.build_num_lit(NumLit::U16(0xFFFE));
    let v = b.build_num_op(Convert(U16, I16), I16, x);
    check(&mut b, v, 254);

    // Widening extends by the source's signedness.
    let x = b.build_num_lit(NumLit::U16(0xFFFF));
    let wide = b.build_num_op(Convert(U16, I64), I64, x);
    let y = b.build_num_lit(NumLit::I64(256));
    let v = b.build_num_binop(Div(I64), I64, wide, y);
    check(&mut b, v, 255);
    let x = b.build_num_lit(NumLit::I16(-1));
    let wide = b.build_num_op(Convert(I16, I32), I32, x);
    let y = b.build_num_lit(NumLit::I32(16));
    let v = b.build_num_binop(ShiftRight(IntType::I32), I32, wide, y);
    check(&mut b, v, 255);

    // Unsigned arithmetic and comparison.
    let x = b.build_num_lit(NumLit::U8(1));
    let v = b.build_num_op(Neg(U8), U8, x);
    check(&mut b, v, 255);
    let x = b.build_num_lit(NumLit::U64(u64::MAX));
    let y = b.build_num_lit(NumLit::U64(2));
    let v = b.build_num_binop(Div(U64), U64, x, y);
    check(&mut b, v, 255);
    let x = b.build_num_lit(NumLit::U16(1));
    let y = b.build_num_lit(NumLit::U16(0xFFFF));
    let args = b.build_tuple(&[x, y]);
    let lt = b.add_binding(Type::Bool, Expr::Intrinsic(Lt(U16), args));
    let one = b.build_num_lit(NumLit::U8(1));
    let zero = b.build_num_lit(NumLit::U8(0));
    let v = b.add_binding(
        Type::Num(U8),
        Expr::If(lt, Box::new(Expr::Local(one)), Box::new(Expr::Local(zero))),
    );
    check(&mut b, v, 1);

    // Arithmetic wraps, shifts are logical, and shift amounts are taken mod the width.
    let x = b.build_num_lit(NumLit::U16(0xFFFF));
    let y = b.build_num_lit(NumLit::U16(1));
    let v = b.build_num_binop(Add(U16), U16, x, y);
    check(&mut b, v, 0);
    let x = b.build_num_lit(NumLit::I8(16));
    let v = b.build_num_binop(Mul(I8), I8, x, x);
    check(&mut b, v, 0);
    let x = b.build_num_lit(NumLit::I16(-32768));
    let y = b.build_num_lit(NumLit::I16(15));
    let v = b.build_num_binop(ShiftRight(IntType::I16), I16, x, y);
    check(&mut b, v, 1);
    let x = b.build_num_lit(NumLit::U16(1));
    let y = b.build_num_lit(NumLit::U16(17));
    let v = b.build_num_binop(ShiftLeft(IntType::U16), U16, x, y);
    check(&mut b, v, 2);
    let x = b.build_num_lit(NumLit::U16(0xFF0F));
    let y = b.build_num_lit(NumLit::U16(0x00FF));
    let v = b.build_num_binop(BitXor(IntType::U16), U16, x, y);
    check(&mut b, v, 0xF0);
    let x = b.build_num_lit(NumLit::F32(1.5));
    let y = b.build_num_lit(NumLit::F32(2.25));
    let v = b.build_num_binop(Add(F32), F32, x, y);
    check(&mut b, v, 3);

    b.build_output(arr);
    assert_eq!(run_for_output(b.finish()), expected);
}
