(* Number types: I8, I16 and U16 are ints wrapped to their width; U8 is char; I32 and U32 are int32; I64 and U64 are int64,
   the unsigned ones as their bit patterns; F32 and F64 are float, since OCaml has no 32-bit float. *)
let wrap_u bits v = let m = 1 lsl bits in ((v mod m) + m) mod m
let wrap_s bits v = let h = 1 lsl (bits - 1) in wrap_u bits (v + h) - h
let popcount_bits bits v = let rec go n acc = if n >= bits then acc else go (n + 1) (acc + ((v lsr n) land 1)) in go 0 0
let clz_bits bits v = let rec go n = if n >= bits then bits else if (v lsr (bits - 1 - n)) land 1 <> 0 then n else go (n + 1) in go 0
let ctz_bits bits v = let rec go n = if n >= bits then bits else if (v lsr n) land 1 <> 0 then n else go (n + 1) in go 0
let popcount64 x = let rec go n acc = if n >= 64 then acc else if Int64.logand (Int64.shift_right_logical x n) 1L = 1L then go (n + 1) (acc + 1) else go (n + 1) acc in go 0 0
let clz64 x = let rec go n = if n >= 64 then 64 else if Int64.logand (Int64.shift_right_logical x (63 - n)) 1L <> 0L then n else go (n + 1) in go 0
let ctz64 x = let rec go n = if n >= 64 then 64 else if Int64.logand x (Int64.shift_left 1L n) <> 0L then n else go (n + 1) in go 0
let intrinsic_AddI8 ((x, y) : int * int): int = wrap_s 8 (x + y)
let intrinsic_AddI16 ((x, y) : int * int): int = wrap_s 16 (x + y)
let intrinsic_AddI32 ((x, y) : int32 * int32): int32 = Int32.add x y
let intrinsic_AddI64 ((x, y) : int64 * int64): int64 = Int64.add x y
let intrinsic_AddU8 ((x, y) : char * char): char = Char.chr (((Char.code x + Char.code y) mod 256 + 256) mod 256)
let intrinsic_AddU16 ((x, y) : int * int): int = wrap_u 16 (x + y)
let intrinsic_AddU32 ((x, y) : int32 * int32): int32 = Int32.add x y
let intrinsic_AddU64 ((x, y) : int64 * int64): int64 = Int64.add x y
let intrinsic_AddF32 ((x, y) : float * float): float = x +. y
let intrinsic_AddF64 ((x, y) : float * float): float = x +. y
let intrinsic_SubI8 ((x, y) : int * int): int = wrap_s 8 (x - y)
let intrinsic_SubI16 ((x, y) : int * int): int = wrap_s 16 (x - y)
let intrinsic_SubI32 ((x, y) : int32 * int32): int32 = Int32.sub x y
let intrinsic_SubI64 ((x, y) : int64 * int64): int64 = Int64.sub x y
let intrinsic_SubU8 ((x, y) : char * char): char = Char.chr (((Char.code x - Char.code y) mod 256 + 256) mod 256)
let intrinsic_SubU16 ((x, y) : int * int): int = wrap_u 16 (x - y)
let intrinsic_SubU32 ((x, y) : int32 * int32): int32 = Int32.sub x y
let intrinsic_SubU64 ((x, y) : int64 * int64): int64 = Int64.sub x y
let intrinsic_SubF32 ((x, y) : float * float): float = x -. y
let intrinsic_SubF64 ((x, y) : float * float): float = x -. y
let intrinsic_MulI8 ((x, y) : int * int): int = wrap_s 8 (x * y)
let intrinsic_MulI16 ((x, y) : int * int): int = wrap_s 16 (x * y)
let intrinsic_MulI32 ((x, y) : int32 * int32): int32 = Int32.mul x y
let intrinsic_MulI64 ((x, y) : int64 * int64): int64 = Int64.mul x y
let intrinsic_MulU8 ((x, y) : char * char): char = Char.chr (((Char.code x * Char.code y) mod 256 + 256) mod 256)
let intrinsic_MulU16 ((x, y) : int * int): int = wrap_u 16 (x * y)
let intrinsic_MulU32 ((x, y) : int32 * int32): int32 = Int32.mul x y
let intrinsic_MulU64 ((x, y) : int64 * int64): int64 = Int64.mul x y
let intrinsic_MulF32 ((x, y) : float * float): float = x *. y
let intrinsic_MulF64 ((x, y) : float * float): float = x *. y
let intrinsic_DivI8 ((x, y) : int * int): int = wrap_s 8 (x / y)
let intrinsic_DivI16 ((x, y) : int * int): int = wrap_s 16 (x / y)
let intrinsic_DivI32 ((x, y) : int32 * int32): int32 = Int32.div x y
let intrinsic_DivI64 ((x, y) : int64 * int64): int64 = Int64.div x y
let intrinsic_DivU8 ((x, y) : char * char): char = Char.chr (((Char.code x / Char.code y) mod 256 + 256) mod 256)
let intrinsic_DivU16 ((x, y) : int * int): int = wrap_u 16 (x / y)
let intrinsic_DivU32 ((x, y) : int32 * int32): int32 = Int32.unsigned_div x y
let intrinsic_DivU64 ((x, y) : int64 * int64): int64 = Int64.unsigned_div x y
let intrinsic_DivF32 ((x, y) : float * float): float = x /. y
let intrinsic_DivF64 ((x, y) : float * float): float = x /. y
let intrinsic_NegI8 (x : int) : int = wrap_s 8 (-x)
let intrinsic_NegI16 (x : int) : int = wrap_s 16 (-x)
let intrinsic_NegI32 (x : int32) : int32 = Int32.neg x
let intrinsic_NegI64 (x : int64) : int64 = Int64.neg x
let intrinsic_NegU8 (x : char) : char = Char.chr (((-Char.code x) mod 256 + 256) mod 256)
let intrinsic_NegU16 (x : int) : int = wrap_u 16 (-x)
let intrinsic_NegU32 (x : int32) : int32 = Int32.neg x
let intrinsic_NegU64 (x : int64) : int64 = Int64.neg x
let intrinsic_NegF32 (x : float) : float = -.x
let intrinsic_NegF64 (x : float) : float = -.x
let intrinsic_EqI8 ((x, y) : int * int): bool = x = y
let intrinsic_EqI16 ((x, y) : int * int): bool = x = y
let intrinsic_EqI32 ((x, y) : int32 * int32): bool = x = y
let intrinsic_EqI64 ((x, y) : int64 * int64): bool = x = y
let intrinsic_EqU8 ((x, y) : char * char): bool = x = y
let intrinsic_EqU16 ((x, y) : int * int): bool = x = y
let intrinsic_EqU32 ((x, y) : int32 * int32): bool = x = y
let intrinsic_EqU64 ((x, y) : int64 * int64): bool = x = y
let intrinsic_EqF32 ((x, y) : float * float): bool = x = y
let intrinsic_EqF64 ((x, y) : float * float): bool = x = y
let intrinsic_LtI8 ((x, y) : int * int): bool = x < y
let intrinsic_LtI16 ((x, y) : int * int): bool = x < y
let intrinsic_LtI32 ((x, y) : int32 * int32): bool = x < y
let intrinsic_LtI64 ((x, y) : int64 * int64): bool = x < y
let intrinsic_LtU8 ((x, y) : char * char): bool = x < y
let intrinsic_LtU16 ((x, y) : int * int): bool = x < y
let intrinsic_LtU32 ((x, y) : int32 * int32): bool = Int32.unsigned_compare x y < 0
let intrinsic_LtU64 ((x, y) : int64 * int64): bool = Int64.unsigned_compare x y < 0
let intrinsic_LtF32 ((x, y) : float * float): bool = x < y
let intrinsic_LtF64 ((x, y) : float * float): bool = x < y
let intrinsic_LteI8 ((x, y) : int * int): bool = x <= y
let intrinsic_LteI16 ((x, y) : int * int): bool = x <= y
let intrinsic_LteI32 ((x, y) : int32 * int32): bool = x <= y
let intrinsic_LteI64 ((x, y) : int64 * int64): bool = x <= y
let intrinsic_LteU8 ((x, y) : char * char): bool = x <= y
let intrinsic_LteU16 ((x, y) : int * int): bool = x <= y
let intrinsic_LteU32 ((x, y) : int32 * int32): bool = Int32.unsigned_compare x y <= 0
let intrinsic_LteU64 ((x, y) : int64 * int64): bool = Int64.unsigned_compare x y <= 0
let intrinsic_LteF32 ((x, y) : float * float): bool = x <= y
let intrinsic_LteF64 ((x, y) : float * float): bool = x <= y
let intrinsic_GtI8 ((x, y) : int * int): bool = x > y
let intrinsic_GtI16 ((x, y) : int * int): bool = x > y
let intrinsic_GtI32 ((x, y) : int32 * int32): bool = x > y
let intrinsic_GtI64 ((x, y) : int64 * int64): bool = x > y
let intrinsic_GtU8 ((x, y) : char * char): bool = x > y
let intrinsic_GtU16 ((x, y) : int * int): bool = x > y
let intrinsic_GtU32 ((x, y) : int32 * int32): bool = Int32.unsigned_compare x y > 0
let intrinsic_GtU64 ((x, y) : int64 * int64): bool = Int64.unsigned_compare x y > 0
let intrinsic_GtF32 ((x, y) : float * float): bool = x > y
let intrinsic_GtF64 ((x, y) : float * float): bool = x > y
let intrinsic_GteI8 ((x, y) : int * int): bool = x >= y
let intrinsic_GteI16 ((x, y) : int * int): bool = x >= y
let intrinsic_GteI32 ((x, y) : int32 * int32): bool = x >= y
let intrinsic_GteI64 ((x, y) : int64 * int64): bool = x >= y
let intrinsic_GteU8 ((x, y) : char * char): bool = x >= y
let intrinsic_GteU16 ((x, y) : int * int): bool = x >= y
let intrinsic_GteU32 ((x, y) : int32 * int32): bool = Int32.unsigned_compare x y >= 0
let intrinsic_GteU64 ((x, y) : int64 * int64): bool = Int64.unsigned_compare x y >= 0
let intrinsic_GteF32 ((x, y) : float * float): bool = x >= y
let intrinsic_GteF64 ((x, y) : float * float): bool = x >= y
let intrinsic_EqBool ((x, y) : bool * bool): bool = x = y
let intrinsic_Not (x : bool) : bool = not x
let intrinsic_I8BitAnd ((x, y) : int * int): int = wrap_s 8 (x land y)
let intrinsic_I16BitAnd ((x, y) : int * int): int = wrap_s 16 (x land y)
let intrinsic_I32BitAnd ((x, y) : int32 * int32): int32 = Int32.logand x y
let intrinsic_I64BitAnd ((x, y) : int64 * int64): int64 = Int64.logand x y
let intrinsic_U8BitAnd ((x, y) : char * char): char = Char.chr (Char.code x land Char.code y)
let intrinsic_U16BitAnd ((x, y) : int * int): int = wrap_u 16 (x land y)
let intrinsic_U32BitAnd ((x, y) : int32 * int32): int32 = Int32.logand x y
let intrinsic_U64BitAnd ((x, y) : int64 * int64): int64 = Int64.logand x y
let intrinsic_I8BitOr ((x, y) : int * int): int = wrap_s 8 (x lor y)
let intrinsic_I16BitOr ((x, y) : int * int): int = wrap_s 16 (x lor y)
let intrinsic_I32BitOr ((x, y) : int32 * int32): int32 = Int32.logor x y
let intrinsic_I64BitOr ((x, y) : int64 * int64): int64 = Int64.logor x y
let intrinsic_U8BitOr ((x, y) : char * char): char = Char.chr (Char.code x lor Char.code y)
let intrinsic_U16BitOr ((x, y) : int * int): int = wrap_u 16 (x lor y)
let intrinsic_U32BitOr ((x, y) : int32 * int32): int32 = Int32.logor x y
let intrinsic_U64BitOr ((x, y) : int64 * int64): int64 = Int64.logor x y
let intrinsic_I8BitXor ((x, y) : int * int): int = wrap_s 8 (x lxor y)
let intrinsic_I16BitXor ((x, y) : int * int): int = wrap_s 16 (x lxor y)
let intrinsic_I32BitXor ((x, y) : int32 * int32): int32 = Int32.logxor x y
let intrinsic_I64BitXor ((x, y) : int64 * int64): int64 = Int64.logxor x y
let intrinsic_U8BitXor ((x, y) : char * char): char = Char.chr (Char.code x lxor Char.code y)
let intrinsic_U16BitXor ((x, y) : int * int): int = wrap_u 16 (x lxor y)
let intrinsic_U32BitXor ((x, y) : int32 * int32): int32 = Int32.logxor x y
let intrinsic_U64BitXor ((x, y) : int64 * int64): int64 = Int64.logxor x y
let intrinsic_I8BitNot (x : int) : int = wrap_s 8 (lnot x)
let intrinsic_I16BitNot (x : int) : int = wrap_s 16 (lnot x)
let intrinsic_I32BitNot (x : int32) : int32 = Int32.lognot x
let intrinsic_I64BitNot (x : int64) : int64 = Int64.lognot x
let intrinsic_U8BitNot (x : char) : char = Char.chr (255 - Char.code x)
let intrinsic_U16BitNot (x : int) : int = wrap_u 16 (lnot x)
let intrinsic_U32BitNot (x : int32) : int32 = Int32.lognot x
let intrinsic_U64BitNot (x : int64) : int64 = Int64.lognot x
let intrinsic_I8ShiftLeft ((x, y) : int * int): int = wrap_s 8 (x lsl (y land 7))
let intrinsic_I16ShiftLeft ((x, y) : int * int): int = wrap_s 16 (x lsl (y land 15))
let intrinsic_I32ShiftLeft ((x, y) : int32 * int32): int32 = Int32.shift_left x (Int32.to_int y land 31)
let intrinsic_I64ShiftLeft ((x, y) : int64 * int64): int64 = Int64.shift_left x (Int64.to_int y land 63)
let intrinsic_U8ShiftLeft ((x, y) : char * char): char = Char.chr ((Char.code x lsl (Char.code y land 7)) land 255)
let intrinsic_U16ShiftLeft ((x, y) : int * int): int = wrap_u 16 (x lsl (y land 15))
let intrinsic_U32ShiftLeft ((x, y) : int32 * int32): int32 = Int32.shift_left x (Int32.to_int y land 31)
let intrinsic_U64ShiftLeft ((x, y) : int64 * int64): int64 = Int64.shift_left x (Int64.to_int y land 63)
let intrinsic_I8ShiftRight ((x, y) : int * int): int = wrap_s 8 ((x land 255) lsr (y land 7))
let intrinsic_I16ShiftRight ((x, y) : int * int): int = wrap_s 16 ((x land 65535) lsr (y land 15))
let intrinsic_I32ShiftRight ((x, y) : int32 * int32): int32 = Int32.shift_right_logical x (Int32.to_int y land 31)
let intrinsic_I64ShiftRight ((x, y) : int64 * int64): int64 = Int64.shift_right_logical x (Int64.to_int y land 63)
let intrinsic_U8ShiftRight ((x, y) : char * char): char = Char.chr (Char.code x lsr (Char.code y land 7))
let intrinsic_U16ShiftRight ((x, y) : int * int): int = wrap_u 16 ((x land 65535) lsr (y land 15))
let intrinsic_U32ShiftRight ((x, y) : int32 * int32): int32 = Int32.shift_right_logical x (Int32.to_int y land 31)
let intrinsic_U64ShiftRight ((x, y) : int64 * int64): int64 = Int64.shift_right_logical x (Int64.to_int y land 63)
let intrinsic_I8Ctpop (x : int) : int = popcount_bits 8 (x land 255)
let intrinsic_I16Ctpop (x : int) : int = popcount_bits 16 (x land 65535)
let intrinsic_I32Ctpop (x : int32) : int32 = Int32.of_int (popcount_bits 32 (Int32.to_int x land 0xFFFFFFFF))
let intrinsic_I64Ctpop (x : int64) : int64 = Int64.of_int (popcount64 x)
let intrinsic_U8Ctpop (x : char) : char = Char.chr (popcount_bits 8 (Char.code x))
let intrinsic_U16Ctpop (x : int) : int = popcount_bits 16 (x land 65535)
let intrinsic_U32Ctpop (x : int32) : int32 = Int32.of_int (popcount_bits 32 (Int32.to_int x land 0xFFFFFFFF))
let intrinsic_U64Ctpop (x : int64) : int64 = Int64.of_int (popcount64 x)
let intrinsic_I8Ctlz (x : int) : int = clz_bits 8 (x land 255)
let intrinsic_I16Ctlz (x : int) : int = clz_bits 16 (x land 65535)
let intrinsic_I32Ctlz (x : int32) : int32 = Int32.of_int (clz_bits 32 (Int32.to_int x land 0xFFFFFFFF))
let intrinsic_I64Ctlz (x : int64) : int64 = Int64.of_int (clz64 x)
let intrinsic_U8Ctlz (x : char) : char = Char.chr (clz_bits 8 (Char.code x))
let intrinsic_U16Ctlz (x : int) : int = clz_bits 16 (x land 65535)
let intrinsic_U32Ctlz (x : int32) : int32 = Int32.of_int (clz_bits 32 (Int32.to_int x land 0xFFFFFFFF))
let intrinsic_U64Ctlz (x : int64) : int64 = Int64.of_int (clz64 x)
let intrinsic_I8Cttz (x : int) : int = ctz_bits 8 (x land 255)
let intrinsic_I16Cttz (x : int) : int = ctz_bits 16 (x land 65535)
let intrinsic_I32Cttz (x : int32) : int32 = Int32.of_int (ctz_bits 32 (Int32.to_int x land 0xFFFFFFFF))
let intrinsic_I64Cttz (x : int64) : int64 = Int64.of_int (ctz64 x)
let intrinsic_U8Cttz (x : char) : char = Char.chr (ctz_bits 8 (Char.code x))
let intrinsic_U16Cttz (x : int) : int = ctz_bits 16 (x land 65535)
let intrinsic_U32Cttz (x : int32) : int32 = Int32.of_int (ctz_bits 32 (Int32.to_int x land 0xFFFFFFFF))
let intrinsic_U64Cttz (x : int64) : int64 = Int64.of_int (ctz64 x)
let intrinsic_I8ToI16 (x : int) : int = wrap_s 16 (Int64.to_int (Int64.of_int x))
let intrinsic_I8ToI32 (x : int) : int32 = Int64.to_int32 (Int64.of_int x)
let intrinsic_I8ToI64 (x : int) : int64 = Int64.of_int x
let intrinsic_I8ToU8 (x : int) : char = Char.chr (wrap_u 8 (Int64.to_int (Int64.of_int x)))
let intrinsic_I8ToU16 (x : int) : int = wrap_u 16 (Int64.to_int (Int64.of_int x))
let intrinsic_I8ToU32 (x : int) : int32 = Int64.to_int32 (Int64.of_int x)
let intrinsic_I8ToU64 (x : int) : int64 = Int64.of_int x
let intrinsic_I8ToF32 (x : int) : float = Int64.to_float (Int64.of_int x)
let intrinsic_I8ToF64 (x : int) : float = Int64.to_float (Int64.of_int x)
let intrinsic_I16ToI8 (x : int) : int = wrap_s 8 (Int64.to_int (Int64.of_int x))
let intrinsic_I16ToI32 (x : int) : int32 = Int64.to_int32 (Int64.of_int x)
let intrinsic_I16ToI64 (x : int) : int64 = Int64.of_int x
let intrinsic_I16ToU8 (x : int) : char = Char.chr (wrap_u 8 (Int64.to_int (Int64.of_int x)))
let intrinsic_I16ToU16 (x : int) : int = wrap_u 16 (Int64.to_int (Int64.of_int x))
let intrinsic_I16ToU32 (x : int) : int32 = Int64.to_int32 (Int64.of_int x)
let intrinsic_I16ToU64 (x : int) : int64 = Int64.of_int x
let intrinsic_I16ToF32 (x : int) : float = Int64.to_float (Int64.of_int x)
let intrinsic_I16ToF64 (x : int) : float = Int64.to_float (Int64.of_int x)
let intrinsic_I32ToI8 (x : int32) : int = wrap_s 8 (Int64.to_int (Int64.of_int32 x))
let intrinsic_I32ToI16 (x : int32) : int = wrap_s 16 (Int64.to_int (Int64.of_int32 x))
let intrinsic_I32ToI64 (x : int32) : int64 = Int64.of_int32 x
let intrinsic_I32ToU8 (x : int32) : char = Char.chr (wrap_u 8 (Int64.to_int (Int64.of_int32 x)))
let intrinsic_I32ToU16 (x : int32) : int = wrap_u 16 (Int64.to_int (Int64.of_int32 x))
let intrinsic_I32ToU32 (x : int32) : int32 = Int64.to_int32 (Int64.of_int32 x)
let intrinsic_I32ToU64 (x : int32) : int64 = Int64.of_int32 x
let intrinsic_I32ToF32 (x : int32) : float = Int64.to_float (Int64.of_int32 x)
let intrinsic_I32ToF64 (x : int32) : float = Int64.to_float (Int64.of_int32 x)
let intrinsic_I64ToI8 (x : int64) : int = wrap_s 8 (Int64.to_int (x))
let intrinsic_I64ToI16 (x : int64) : int = wrap_s 16 (Int64.to_int (x))
let intrinsic_I64ToI32 (x : int64) : int32 = Int64.to_int32 (x)
let intrinsic_I64ToU8 (x : int64) : char = Char.chr (wrap_u 8 (Int64.to_int (x)))
let intrinsic_I64ToU16 (x : int64) : int = wrap_u 16 (Int64.to_int (x))
let intrinsic_I64ToU32 (x : int64) : int32 = Int64.to_int32 (x)
let intrinsic_I64ToU64 (x : int64) : int64 = x
let intrinsic_I64ToF32 (x : int64) : float = Int64.to_float (x)
let intrinsic_I64ToF64 (x : int64) : float = Int64.to_float (x)
let intrinsic_U8ToI8 (x : char) : int = wrap_s 8 (Int64.to_int (Int64.of_int (Char.code x)))
let intrinsic_U8ToI16 (x : char) : int = wrap_s 16 (Int64.to_int (Int64.of_int (Char.code x)))
let intrinsic_U8ToI32 (x : char) : int32 = Int64.to_int32 (Int64.of_int (Char.code x))
let intrinsic_U8ToI64 (x : char) : int64 = Int64.of_int (Char.code x)
let intrinsic_U8ToU16 (x : char) : int = wrap_u 16 (Int64.to_int (Int64.of_int (Char.code x)))
let intrinsic_U8ToU32 (x : char) : int32 = Int64.to_int32 (Int64.of_int (Char.code x))
let intrinsic_U8ToU64 (x : char) : int64 = Int64.of_int (Char.code x)
let intrinsic_U8ToF32 (x : char) : float = Int64.to_float (Int64.of_int (Char.code x))
let intrinsic_U8ToF64 (x : char) : float = Int64.to_float (Int64.of_int (Char.code x))
let intrinsic_U16ToI8 (x : int) : int = wrap_s 8 (Int64.to_int (Int64.of_int x))
let intrinsic_U16ToI16 (x : int) : int = wrap_s 16 (Int64.to_int (Int64.of_int x))
let intrinsic_U16ToI32 (x : int) : int32 = Int64.to_int32 (Int64.of_int x)
let intrinsic_U16ToI64 (x : int) : int64 = Int64.of_int x
let intrinsic_U16ToU8 (x : int) : char = Char.chr (wrap_u 8 (Int64.to_int (Int64.of_int x)))
let intrinsic_U16ToU32 (x : int) : int32 = Int64.to_int32 (Int64.of_int x)
let intrinsic_U16ToU64 (x : int) : int64 = Int64.of_int x
let intrinsic_U16ToF32 (x : int) : float = Int64.to_float (Int64.of_int x)
let intrinsic_U16ToF64 (x : int) : float = Int64.to_float (Int64.of_int x)
let intrinsic_U32ToI8 (x : int32) : int = wrap_s 8 (Int64.to_int (Int64.logand (Int64.of_int32 x) 0xFFFFFFFFL))
let intrinsic_U32ToI16 (x : int32) : int = wrap_s 16 (Int64.to_int (Int64.logand (Int64.of_int32 x) 0xFFFFFFFFL))
let intrinsic_U32ToI32 (x : int32) : int32 = Int64.to_int32 (Int64.logand (Int64.of_int32 x) 0xFFFFFFFFL)
let intrinsic_U32ToI64 (x : int32) : int64 = Int64.logand (Int64.of_int32 x) 0xFFFFFFFFL
let intrinsic_U32ToU8 (x : int32) : char = Char.chr (wrap_u 8 (Int64.to_int (Int64.logand (Int64.of_int32 x) 0xFFFFFFFFL)))
let intrinsic_U32ToU16 (x : int32) : int = wrap_u 16 (Int64.to_int (Int64.logand (Int64.of_int32 x) 0xFFFFFFFFL))
let intrinsic_U32ToU64 (x : int32) : int64 = Int64.logand (Int64.of_int32 x) 0xFFFFFFFFL
let intrinsic_U32ToF32 (x : int32) : float = Int64.to_float (Int64.logand (Int64.of_int32 x) 0xFFFFFFFFL)
let intrinsic_U32ToF64 (x : int32) : float = Int64.to_float (Int64.logand (Int64.of_int32 x) 0xFFFFFFFFL)
let intrinsic_U64ToI8 (x : int64) : int = wrap_s 8 (Int64.to_int (x))
let intrinsic_U64ToI16 (x : int64) : int = wrap_s 16 (Int64.to_int (x))
let intrinsic_U64ToI32 (x : int64) : int32 = Int64.to_int32 (x)
let intrinsic_U64ToI64 (x : int64) : int64 = x
let intrinsic_U64ToU8 (x : int64) : char = Char.chr (wrap_u 8 (Int64.to_int (x)))
let intrinsic_U64ToU16 (x : int64) : int = wrap_u 16 (Int64.to_int (x))
let intrinsic_U64ToU32 (x : int64) : int32 = Int64.to_int32 (x)
let intrinsic_U64ToF32 (x : int64) : float = if x >= 0L then Int64.to_float x else Int64.to_float (Int64.shift_right_logical x 1) *. 2.0 +. Int64.to_float (Int64.logand x 1L)
let intrinsic_U64ToF64 (x : int64) : float = if x >= 0L then Int64.to_float x else Int64.to_float (Int64.shift_right_logical x 1) *. 2.0 +. Int64.to_float (Int64.logand x 1L)
let intrinsic_F32ToI8 (x : float) : int = wrap_s 8 (Int64.to_int (if x <> x then 0L else if x <= -128.0 then -128L else if x >= 127.0 then 127L else Int64.of_float x))
let intrinsic_F32ToI16 (x : float) : int = wrap_s 16 (Int64.to_int (if x <> x then 0L else if x <= -32768.0 then -32768L else if x >= 32767.0 then 32767L else Int64.of_float x))
let intrinsic_F32ToI32 (x : float) : int32 = Int64.to_int32 (if x <> x then 0L else if x <= -2147483648.0 then -2147483648L else if x >= 2147483647.0 then 2147483647L else Int64.of_float x)
let intrinsic_F32ToI64 (x : float) : int64 = if x <> x then 0L else if x <= -9.223372036854776e+18 then -9223372036854775808L else if x >= 9.223372036854776e+18 then 9223372036854775807L else Int64.of_float x
let intrinsic_F32ToU8 (x : float) : char = Char.chr (wrap_u 8 (Int64.to_int (if x <> x then 0L else if x <= 0.0 then 0L else if x >= 255.0 then 255L else Int64.of_float x)))
let intrinsic_F32ToU16 (x : float) : int = wrap_u 16 (Int64.to_int (if x <> x then 0L else if x <= 0.0 then 0L else if x >= 65535.0 then 65535L else Int64.of_float x))
let intrinsic_F32ToU32 (x : float) : int32 = Int64.to_int32 (if x <> x then 0L else if x <= 0.0 then 0L else if x >= 4294967295.0 then 4294967295L else Int64.of_float x)
let intrinsic_F32ToU64 (x : float) : int64 = if x <> x || x <= 0.0 then 0L else if x >= 18446744073709551615.0 then (-1L) else if x >= 9223372036854775808.0 then Int64.add (Int64.of_float (x -. 9223372036854775808.0)) Int64.min_int else Int64.of_float x
let intrinsic_F32ToF64 (x : float) : float = x
let intrinsic_F64ToI8 (x : float) : int = wrap_s 8 (Int64.to_int (if x <> x then 0L else if x <= -128.0 then -128L else if x >= 127.0 then 127L else Int64.of_float x))
let intrinsic_F64ToI16 (x : float) : int = wrap_s 16 (Int64.to_int (if x <> x then 0L else if x <= -32768.0 then -32768L else if x >= 32767.0 then 32767L else Int64.of_float x))
let intrinsic_F64ToI32 (x : float) : int32 = Int64.to_int32 (if x <> x then 0L else if x <= -2147483648.0 then -2147483648L else if x >= 2147483647.0 then 2147483647L else Int64.of_float x)
let intrinsic_F64ToI64 (x : float) : int64 = if x <> x then 0L else if x <= -9.223372036854776e+18 then -9223372036854775808L else if x >= 9.223372036854776e+18 then 9223372036854775807L else Int64.of_float x
let intrinsic_F64ToU8 (x : float) : char = Char.chr (wrap_u 8 (Int64.to_int (if x <> x then 0L else if x <= 0.0 then 0L else if x >= 255.0 then 255L else Int64.of_float x)))
let intrinsic_F64ToU16 (x : float) : int = wrap_u 16 (Int64.to_int (if x <> x then 0L else if x <= 0.0 then 0L else if x >= 65535.0 then 65535L else Int64.of_float x))
let intrinsic_F64ToU32 (x : float) : int32 = Int64.to_int32 (if x <> x then 0L else if x <= 0.0 then 0L else if x >= 4294967295.0 then 4294967295L else Int64.of_float x)
let intrinsic_F64ToU64 (x : float) : int64 = if x <> x || x <= 0.0 then 0L else if x >= 18446744073709551615.0 then (-1L) else if x >= 9223372036854775808.0 then Int64.add (Int64.of_float (x -. 9223372036854775808.0)) Int64.min_int else Int64.of_float x
let intrinsic_F64ToF32 (x : float) : float = Int32.float_of_bits (Int32.bits_of_float x)


let intrinsic_get ((l, i) : 'a PersistentArray.array * int64): 'a = PersistentArray.sub (l, (Int64.to_int i))
let intrinsic_extract ((l, i) : 'a PersistentArray.array * int64): 'a * ('a -> 'a PersistentArray.array) = (PersistentArray.sub (l, (Int64.to_int i)), fun new_ -> PersistentArray.update (l, Int64.to_int i, new_))
let intrinsic_len (l : 'a PersistentArray.array): int64 = Int64.of_int (PersistentArray.length l)
let intrinsic_push ((l, x) : 'a PersistentArray.array * 'a): 'a PersistentArray.array = PersistentArray.append (l, x)
let intrinsic_pop (l : 'a PersistentArray.array): 'a PersistentArray.array * 'a = PersistentArray.popEnd(l)
let intrinsic_reserve ((l, i) : 'a PersistentArray.array * int64): 'a PersistentArray.array = l
let intrinsic_replace((f, x) : ('a -> 'a PersistentArray.array) * 'a): 'a PersistentArray.array = f x

let input (()) : char PersistentArray.array = let in_ = try read_line () with End_of_file -> "" in PersistentArray.fromList (Array.init (String.length in_) (String.get in_))
let output (l : char PersistentArray.array) = print_string (String.init (PersistentArray.length l) (fun i -> PersistentArray.sub (l, i)))
let panic (l : char PersistentArray.array) = raise (Failure (String.init (PersistentArray.length l) (fun i -> PersistentArray.sub (l, i))))
