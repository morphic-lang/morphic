(* Number types: I8, I16 and I32 are IntN.int; I64 is Int.int; U8 is char; U16, U32 and U64 are WordN.word; F32 is Real32.real; F64 is real.
   Arithmetic goes through LargeInt and wraps through the word of the type's width. *)
fun popcount64 (0w0 : Word64.word) = 0
  | popcount64 w = Word64.toInt (Word64.andb (w, 0w1)) + popcount64 (Word64.>> (w, 0w1))
fun clz64 (w : Word64.word) = let fun go (w, acc) = if w = 0w0 then 64 else if Word64.andb (Word64.>> (w, 0w63), 0w1) = 0w1 then acc else go (Word64.<< (w, 0w1), acc + 1) in go (w, 0) end
fun ctz64 (w : Word64.word) = let fun go (w, acc) = if w = 0w0 then 64 else if Word64.andb (w, 0w1) = 0w1 then acc else go (Word64.>> (w, 0w1), acc + 1) in go (w, 0) end
fun intrinsic_AddI8(x : Int8.int, y : Int8.int): Int8.int = Int8.fromLarge (Word8.toLargeIntX (Word8.fromLargeInt (Int8.toLarge x + Int8.toLarge y)))
fun intrinsic_AddI16(x : Int16.int, y : Int16.int): Int16.int = Int16.fromLarge (Word16.toLargeIntX (Word16.fromLargeInt (Int16.toLarge x + Int16.toLarge y)))
fun intrinsic_AddI32(x : Int32.int, y : Int32.int): Int32.int = Int32.fromLarge (Word32.toLargeIntX (Word32.fromLargeInt (Int32.toLarge x + Int32.toLarge y)))
fun intrinsic_AddI64(x : Int.int, y : Int.int): Int.int = Word64.toIntX (Word64.fromLargeInt (Int.toLarge x + Int.toLarge y))
fun intrinsic_AddU8(x : char, y : char): char = chr (Word8.toInt (Word8.fromLargeInt (Int.toLarge (ord x) + Int.toLarge (ord y))))
fun intrinsic_AddU16(x : Word16.word, y : Word16.word): Word16.word = Word16.fromLargeInt (Word16.toLargeInt x + Word16.toLargeInt y)
fun intrinsic_AddU32(x : Word32.word, y : Word32.word): Word32.word = Word32.fromLargeInt (Word32.toLargeInt x + Word32.toLargeInt y)
fun intrinsic_AddU64(x : Word64.word, y : Word64.word): Word64.word = Word64.fromLargeInt (Word64.toLargeInt x + Word64.toLargeInt y)
fun intrinsic_AddF32(x : Real32.real, y : Real32.real): Real32.real = x + y
fun intrinsic_AddF64(x : real, y : real): real = x + y
fun intrinsic_SubI8(x : Int8.int, y : Int8.int): Int8.int = Int8.fromLarge (Word8.toLargeIntX (Word8.fromLargeInt (Int8.toLarge x - Int8.toLarge y)))
fun intrinsic_SubI16(x : Int16.int, y : Int16.int): Int16.int = Int16.fromLarge (Word16.toLargeIntX (Word16.fromLargeInt (Int16.toLarge x - Int16.toLarge y)))
fun intrinsic_SubI32(x : Int32.int, y : Int32.int): Int32.int = Int32.fromLarge (Word32.toLargeIntX (Word32.fromLargeInt (Int32.toLarge x - Int32.toLarge y)))
fun intrinsic_SubI64(x : Int.int, y : Int.int): Int.int = Word64.toIntX (Word64.fromLargeInt (Int.toLarge x - Int.toLarge y))
fun intrinsic_SubU8(x : char, y : char): char = chr (Word8.toInt (Word8.fromLargeInt (Int.toLarge (ord x) - Int.toLarge (ord y))))
fun intrinsic_SubU16(x : Word16.word, y : Word16.word): Word16.word = Word16.fromLargeInt (Word16.toLargeInt x - Word16.toLargeInt y)
fun intrinsic_SubU32(x : Word32.word, y : Word32.word): Word32.word = Word32.fromLargeInt (Word32.toLargeInt x - Word32.toLargeInt y)
fun intrinsic_SubU64(x : Word64.word, y : Word64.word): Word64.word = Word64.fromLargeInt (Word64.toLargeInt x - Word64.toLargeInt y)
fun intrinsic_SubF32(x : Real32.real, y : Real32.real): Real32.real = x - y
fun intrinsic_SubF64(x : real, y : real): real = x - y
fun intrinsic_MulI8(x : Int8.int, y : Int8.int): Int8.int = Int8.fromLarge (Word8.toLargeIntX (Word8.fromLargeInt (Int8.toLarge x * Int8.toLarge y)))
fun intrinsic_MulI16(x : Int16.int, y : Int16.int): Int16.int = Int16.fromLarge (Word16.toLargeIntX (Word16.fromLargeInt (Int16.toLarge x * Int16.toLarge y)))
fun intrinsic_MulI32(x : Int32.int, y : Int32.int): Int32.int = Int32.fromLarge (Word32.toLargeIntX (Word32.fromLargeInt (Int32.toLarge x * Int32.toLarge y)))
fun intrinsic_MulI64(x : Int.int, y : Int.int): Int.int = Word64.toIntX (Word64.fromLargeInt (Int.toLarge x * Int.toLarge y))
fun intrinsic_MulU8(x : char, y : char): char = chr (Word8.toInt (Word8.fromLargeInt (Int.toLarge (ord x) * Int.toLarge (ord y))))
fun intrinsic_MulU16(x : Word16.word, y : Word16.word): Word16.word = Word16.fromLargeInt (Word16.toLargeInt x * Word16.toLargeInt y)
fun intrinsic_MulU32(x : Word32.word, y : Word32.word): Word32.word = Word32.fromLargeInt (Word32.toLargeInt x * Word32.toLargeInt y)
fun intrinsic_MulU64(x : Word64.word, y : Word64.word): Word64.word = Word64.fromLargeInt (Word64.toLargeInt x * Word64.toLargeInt y)
fun intrinsic_MulF32(x : Real32.real, y : Real32.real): Real32.real = x * y
fun intrinsic_MulF64(x : real, y : real): real = x * y
fun intrinsic_DivI8(x : Int8.int, y : Int8.int): Int8.int = Int8.fromLarge (Word8.toLargeIntX (Word8.fromLargeInt (LargeInt.quot (Int8.toLarge x, Int8.toLarge y))))
fun intrinsic_DivI16(x : Int16.int, y : Int16.int): Int16.int = Int16.fromLarge (Word16.toLargeIntX (Word16.fromLargeInt (LargeInt.quot (Int16.toLarge x, Int16.toLarge y))))
fun intrinsic_DivI32(x : Int32.int, y : Int32.int): Int32.int = Int32.fromLarge (Word32.toLargeIntX (Word32.fromLargeInt (LargeInt.quot (Int32.toLarge x, Int32.toLarge y))))
fun intrinsic_DivI64(x : Int.int, y : Int.int): Int.int = Word64.toIntX (Word64.fromLargeInt (LargeInt.quot (Int.toLarge x, Int.toLarge y)))
fun intrinsic_DivU8(x : char, y : char): char = chr (Word8.toInt (Word8.fromLargeInt (LargeInt.quot (Int.toLarge (ord x), Int.toLarge (ord y)))))
fun intrinsic_DivU16(x : Word16.word, y : Word16.word): Word16.word = Word16.fromLargeInt (LargeInt.quot (Word16.toLargeInt x, Word16.toLargeInt y))
fun intrinsic_DivU32(x : Word32.word, y : Word32.word): Word32.word = Word32.fromLargeInt (LargeInt.quot (Word32.toLargeInt x, Word32.toLargeInt y))
fun intrinsic_DivU64(x : Word64.word, y : Word64.word): Word64.word = Word64.fromLargeInt (LargeInt.quot (Word64.toLargeInt x, Word64.toLargeInt y))
fun intrinsic_DivF32(x : Real32.real, y : Real32.real): Real32.real = x / y
fun intrinsic_DivF64(x : real, y : real): real = x / y
fun intrinsic_NegI8(x : Int8.int): Int8.int = Int8.fromLarge (Word8.toLargeIntX (Word8.fromLargeInt (~ (Int8.toLarge x))))
fun intrinsic_NegI16(x : Int16.int): Int16.int = Int16.fromLarge (Word16.toLargeIntX (Word16.fromLargeInt (~ (Int16.toLarge x))))
fun intrinsic_NegI32(x : Int32.int): Int32.int = Int32.fromLarge (Word32.toLargeIntX (Word32.fromLargeInt (~ (Int32.toLarge x))))
fun intrinsic_NegI64(x : Int.int): Int.int = Word64.toIntX (Word64.fromLargeInt (~ (Int.toLarge x)))
fun intrinsic_NegU8(x : char): char = chr (Word8.toInt (Word8.fromLargeInt (~ (Int.toLarge (ord x)))))
fun intrinsic_NegU16(x : Word16.word): Word16.word = Word16.fromLargeInt (~ (Word16.toLargeInt x))
fun intrinsic_NegU32(x : Word32.word): Word32.word = Word32.fromLargeInt (~ (Word32.toLargeInt x))
fun intrinsic_NegU64(x : Word64.word): Word64.word = Word64.fromLargeInt (~ (Word64.toLargeInt x))
fun intrinsic_NegF32(x : Real32.real): Real32.real = ~ x
fun intrinsic_NegF64(x : real): real = ~ x
fun intrinsic_EqI8(x : Int8.int, y : Int8.int): bool = x = y
fun intrinsic_EqI16(x : Int16.int, y : Int16.int): bool = x = y
fun intrinsic_EqI32(x : Int32.int, y : Int32.int): bool = x = y
fun intrinsic_EqI64(x : Int.int, y : Int.int): bool = x = y
fun intrinsic_EqU8(x : char, y : char): bool = x = y
fun intrinsic_EqU16(x : Word16.word, y : Word16.word): bool = x = y
fun intrinsic_EqU32(x : Word32.word, y : Word32.word): bool = x = y
fun intrinsic_EqU64(x : Word64.word, y : Word64.word): bool = x = y
fun intrinsic_EqF32(x : Real32.real, y : Real32.real): bool = Real32.== (x, y)
fun intrinsic_EqF64(x : real, y : real): bool = Real.== (x, y)
fun intrinsic_LtI8(x : Int8.int, y : Int8.int): bool = x < y
fun intrinsic_LtI16(x : Int16.int, y : Int16.int): bool = x < y
fun intrinsic_LtI32(x : Int32.int, y : Int32.int): bool = x < y
fun intrinsic_LtI64(x : Int.int, y : Int.int): bool = x < y
fun intrinsic_LtU8(x : char, y : char): bool = x < y
fun intrinsic_LtU16(x : Word16.word, y : Word16.word): bool = x < y
fun intrinsic_LtU32(x : Word32.word, y : Word32.word): bool = x < y
fun intrinsic_LtU64(x : Word64.word, y : Word64.word): bool = x < y
fun intrinsic_LtF32(x : Real32.real, y : Real32.real): bool = x < y
fun intrinsic_LtF64(x : real, y : real): bool = x < y
fun intrinsic_LteI8(x : Int8.int, y : Int8.int): bool = x <= y
fun intrinsic_LteI16(x : Int16.int, y : Int16.int): bool = x <= y
fun intrinsic_LteI32(x : Int32.int, y : Int32.int): bool = x <= y
fun intrinsic_LteI64(x : Int.int, y : Int.int): bool = x <= y
fun intrinsic_LteU8(x : char, y : char): bool = x <= y
fun intrinsic_LteU16(x : Word16.word, y : Word16.word): bool = x <= y
fun intrinsic_LteU32(x : Word32.word, y : Word32.word): bool = x <= y
fun intrinsic_LteU64(x : Word64.word, y : Word64.word): bool = x <= y
fun intrinsic_LteF32(x : Real32.real, y : Real32.real): bool = x <= y
fun intrinsic_LteF64(x : real, y : real): bool = x <= y
fun intrinsic_GtI8(x : Int8.int, y : Int8.int): bool = x > y
fun intrinsic_GtI16(x : Int16.int, y : Int16.int): bool = x > y
fun intrinsic_GtI32(x : Int32.int, y : Int32.int): bool = x > y
fun intrinsic_GtI64(x : Int.int, y : Int.int): bool = x > y
fun intrinsic_GtU8(x : char, y : char): bool = x > y
fun intrinsic_GtU16(x : Word16.word, y : Word16.word): bool = x > y
fun intrinsic_GtU32(x : Word32.word, y : Word32.word): bool = x > y
fun intrinsic_GtU64(x : Word64.word, y : Word64.word): bool = x > y
fun intrinsic_GtF32(x : Real32.real, y : Real32.real): bool = x > y
fun intrinsic_GtF64(x : real, y : real): bool = x > y
fun intrinsic_GteI8(x : Int8.int, y : Int8.int): bool = x >= y
fun intrinsic_GteI16(x : Int16.int, y : Int16.int): bool = x >= y
fun intrinsic_GteI32(x : Int32.int, y : Int32.int): bool = x >= y
fun intrinsic_GteI64(x : Int.int, y : Int.int): bool = x >= y
fun intrinsic_GteU8(x : char, y : char): bool = x >= y
fun intrinsic_GteU16(x : Word16.word, y : Word16.word): bool = x >= y
fun intrinsic_GteU32(x : Word32.word, y : Word32.word): bool = x >= y
fun intrinsic_GteU64(x : Word64.word, y : Word64.word): bool = x >= y
fun intrinsic_GteF32(x : Real32.real, y : Real32.real): bool = x >= y
fun intrinsic_GteF64(x : real, y : real): bool = x >= y
fun intrinsic_EqBool(x : bool, y : bool): bool = x = y
fun intrinsic_Not(x : bool): bool = not x
fun intrinsic_I8BitAnd(x : Int8.int, y : Int8.int): Int8.int = Int8.fromLarge (Word8.toLargeIntX (Word8.andb (Word8.fromLargeInt (Int8.toLarge x), Word8.fromLargeInt (Int8.toLarge y))))
fun intrinsic_I16BitAnd(x : Int16.int, y : Int16.int): Int16.int = Int16.fromLarge (Word16.toLargeIntX (Word16.andb (Word16.fromLargeInt (Int16.toLarge x), Word16.fromLargeInt (Int16.toLarge y))))
fun intrinsic_I32BitAnd(x : Int32.int, y : Int32.int): Int32.int = Int32.fromLarge (Word32.toLargeIntX (Word32.andb (Word32.fromLargeInt (Int32.toLarge x), Word32.fromLargeInt (Int32.toLarge y))))
fun intrinsic_I64BitAnd(x : Int.int, y : Int.int): Int.int = Word64.toIntX (Word64.andb (Word64.fromLargeInt (Int.toLarge x), Word64.fromLargeInt (Int.toLarge y)))
fun intrinsic_U8BitAnd(x : char, y : char): char = chr (Word8.toInt (Word8.andb (Word8.fromLargeInt (Int.toLarge (ord x)), Word8.fromLargeInt (Int.toLarge (ord y)))))
fun intrinsic_U16BitAnd(x : Word16.word, y : Word16.word): Word16.word = Word16.andb (Word16.fromLargeInt (Word16.toLargeInt x), Word16.fromLargeInt (Word16.toLargeInt y))
fun intrinsic_U32BitAnd(x : Word32.word, y : Word32.word): Word32.word = Word32.andb (Word32.fromLargeInt (Word32.toLargeInt x), Word32.fromLargeInt (Word32.toLargeInt y))
fun intrinsic_U64BitAnd(x : Word64.word, y : Word64.word): Word64.word = Word64.andb (Word64.fromLargeInt (Word64.toLargeInt x), Word64.fromLargeInt (Word64.toLargeInt y))
fun intrinsic_I8BitOr(x : Int8.int, y : Int8.int): Int8.int = Int8.fromLarge (Word8.toLargeIntX (Word8.orb (Word8.fromLargeInt (Int8.toLarge x), Word8.fromLargeInt (Int8.toLarge y))))
fun intrinsic_I16BitOr(x : Int16.int, y : Int16.int): Int16.int = Int16.fromLarge (Word16.toLargeIntX (Word16.orb (Word16.fromLargeInt (Int16.toLarge x), Word16.fromLargeInt (Int16.toLarge y))))
fun intrinsic_I32BitOr(x : Int32.int, y : Int32.int): Int32.int = Int32.fromLarge (Word32.toLargeIntX (Word32.orb (Word32.fromLargeInt (Int32.toLarge x), Word32.fromLargeInt (Int32.toLarge y))))
fun intrinsic_I64BitOr(x : Int.int, y : Int.int): Int.int = Word64.toIntX (Word64.orb (Word64.fromLargeInt (Int.toLarge x), Word64.fromLargeInt (Int.toLarge y)))
fun intrinsic_U8BitOr(x : char, y : char): char = chr (Word8.toInt (Word8.orb (Word8.fromLargeInt (Int.toLarge (ord x)), Word8.fromLargeInt (Int.toLarge (ord y)))))
fun intrinsic_U16BitOr(x : Word16.word, y : Word16.word): Word16.word = Word16.orb (Word16.fromLargeInt (Word16.toLargeInt x), Word16.fromLargeInt (Word16.toLargeInt y))
fun intrinsic_U32BitOr(x : Word32.word, y : Word32.word): Word32.word = Word32.orb (Word32.fromLargeInt (Word32.toLargeInt x), Word32.fromLargeInt (Word32.toLargeInt y))
fun intrinsic_U64BitOr(x : Word64.word, y : Word64.word): Word64.word = Word64.orb (Word64.fromLargeInt (Word64.toLargeInt x), Word64.fromLargeInt (Word64.toLargeInt y))
fun intrinsic_I8BitXor(x : Int8.int, y : Int8.int): Int8.int = Int8.fromLarge (Word8.toLargeIntX (Word8.xorb (Word8.fromLargeInt (Int8.toLarge x), Word8.fromLargeInt (Int8.toLarge y))))
fun intrinsic_I16BitXor(x : Int16.int, y : Int16.int): Int16.int = Int16.fromLarge (Word16.toLargeIntX (Word16.xorb (Word16.fromLargeInt (Int16.toLarge x), Word16.fromLargeInt (Int16.toLarge y))))
fun intrinsic_I32BitXor(x : Int32.int, y : Int32.int): Int32.int = Int32.fromLarge (Word32.toLargeIntX (Word32.xorb (Word32.fromLargeInt (Int32.toLarge x), Word32.fromLargeInt (Int32.toLarge y))))
fun intrinsic_I64BitXor(x : Int.int, y : Int.int): Int.int = Word64.toIntX (Word64.xorb (Word64.fromLargeInt (Int.toLarge x), Word64.fromLargeInt (Int.toLarge y)))
fun intrinsic_U8BitXor(x : char, y : char): char = chr (Word8.toInt (Word8.xorb (Word8.fromLargeInt (Int.toLarge (ord x)), Word8.fromLargeInt (Int.toLarge (ord y)))))
fun intrinsic_U16BitXor(x : Word16.word, y : Word16.word): Word16.word = Word16.xorb (Word16.fromLargeInt (Word16.toLargeInt x), Word16.fromLargeInt (Word16.toLargeInt y))
fun intrinsic_U32BitXor(x : Word32.word, y : Word32.word): Word32.word = Word32.xorb (Word32.fromLargeInt (Word32.toLargeInt x), Word32.fromLargeInt (Word32.toLargeInt y))
fun intrinsic_U64BitXor(x : Word64.word, y : Word64.word): Word64.word = Word64.xorb (Word64.fromLargeInt (Word64.toLargeInt x), Word64.fromLargeInt (Word64.toLargeInt y))
fun intrinsic_I8BitNot(x : Int8.int): Int8.int = Int8.fromLarge (Word8.toLargeIntX (Word8.notb (Word8.fromLargeInt (Int8.toLarge x))))
fun intrinsic_I16BitNot(x : Int16.int): Int16.int = Int16.fromLarge (Word16.toLargeIntX (Word16.notb (Word16.fromLargeInt (Int16.toLarge x))))
fun intrinsic_I32BitNot(x : Int32.int): Int32.int = Int32.fromLarge (Word32.toLargeIntX (Word32.notb (Word32.fromLargeInt (Int32.toLarge x))))
fun intrinsic_I64BitNot(x : Int.int): Int.int = Word64.toIntX (Word64.notb (Word64.fromLargeInt (Int.toLarge x)))
fun intrinsic_U8BitNot(x : char): char = chr (Word8.toInt (Word8.notb (Word8.fromLargeInt (Int.toLarge (ord x)))))
fun intrinsic_U16BitNot(x : Word16.word): Word16.word = Word16.notb (Word16.fromLargeInt (Word16.toLargeInt x))
fun intrinsic_U32BitNot(x : Word32.word): Word32.word = Word32.notb (Word32.fromLargeInt (Word32.toLargeInt x))
fun intrinsic_U64BitNot(x : Word64.word): Word64.word = Word64.notb (Word64.fromLargeInt (Word64.toLargeInt x))
fun intrinsic_I8ShiftLeft(x : Int8.int, y : Int8.int): Int8.int = Int8.fromLarge (Word8.toLargeIntX (Word8.<< (Word8.fromLargeInt (Int8.toLarge x), Word.fromInt (LargeInt.toInt (LargeInt.mod (Int8.toLarge y, 8))))))
fun intrinsic_I16ShiftLeft(x : Int16.int, y : Int16.int): Int16.int = Int16.fromLarge (Word16.toLargeIntX (Word16.<< (Word16.fromLargeInt (Int16.toLarge x), Word.fromInt (LargeInt.toInt (LargeInt.mod (Int16.toLarge y, 16))))))
fun intrinsic_I32ShiftLeft(x : Int32.int, y : Int32.int): Int32.int = Int32.fromLarge (Word32.toLargeIntX (Word32.<< (Word32.fromLargeInt (Int32.toLarge x), Word.fromInt (LargeInt.toInt (LargeInt.mod (Int32.toLarge y, 32))))))
fun intrinsic_I64ShiftLeft(x : Int.int, y : Int.int): Int.int = Word64.toIntX (Word64.<< (Word64.fromLargeInt (Int.toLarge x), Word.fromInt (LargeInt.toInt (LargeInt.mod (Int.toLarge y, 64)))))
fun intrinsic_U8ShiftLeft(x : char, y : char): char = chr (Word8.toInt (Word8.<< (Word8.fromLargeInt (Int.toLarge (ord x)), Word.fromInt (LargeInt.toInt (LargeInt.mod (Int.toLarge (ord y), 8))))))
fun intrinsic_U16ShiftLeft(x : Word16.word, y : Word16.word): Word16.word = Word16.<< (Word16.fromLargeInt (Word16.toLargeInt x), Word.fromInt (LargeInt.toInt (LargeInt.mod (Word16.toLargeInt y, 16))))
fun intrinsic_U32ShiftLeft(x : Word32.word, y : Word32.word): Word32.word = Word32.<< (Word32.fromLargeInt (Word32.toLargeInt x), Word.fromInt (LargeInt.toInt (LargeInt.mod (Word32.toLargeInt y, 32))))
fun intrinsic_U64ShiftLeft(x : Word64.word, y : Word64.word): Word64.word = Word64.<< (Word64.fromLargeInt (Word64.toLargeInt x), Word.fromInt (LargeInt.toInt (LargeInt.mod (Word64.toLargeInt y, 64))))
fun intrinsic_I8ShiftRight(x : Int8.int, y : Int8.int): Int8.int = Int8.fromLarge (Word8.toLargeIntX (Word8.>> (Word8.fromLargeInt (Int8.toLarge x), Word.fromInt (LargeInt.toInt (LargeInt.mod (Int8.toLarge y, 8))))))
fun intrinsic_I16ShiftRight(x : Int16.int, y : Int16.int): Int16.int = Int16.fromLarge (Word16.toLargeIntX (Word16.>> (Word16.fromLargeInt (Int16.toLarge x), Word.fromInt (LargeInt.toInt (LargeInt.mod (Int16.toLarge y, 16))))))
fun intrinsic_I32ShiftRight(x : Int32.int, y : Int32.int): Int32.int = Int32.fromLarge (Word32.toLargeIntX (Word32.>> (Word32.fromLargeInt (Int32.toLarge x), Word.fromInt (LargeInt.toInt (LargeInt.mod (Int32.toLarge y, 32))))))
fun intrinsic_I64ShiftRight(x : Int.int, y : Int.int): Int.int = Word64.toIntX (Word64.>> (Word64.fromLargeInt (Int.toLarge x), Word.fromInt (LargeInt.toInt (LargeInt.mod (Int.toLarge y, 64)))))
fun intrinsic_U8ShiftRight(x : char, y : char): char = chr (Word8.toInt (Word8.>> (Word8.fromLargeInt (Int.toLarge (ord x)), Word.fromInt (LargeInt.toInt (LargeInt.mod (Int.toLarge (ord y), 8))))))
fun intrinsic_U16ShiftRight(x : Word16.word, y : Word16.word): Word16.word = Word16.>> (Word16.fromLargeInt (Word16.toLargeInt x), Word.fromInt (LargeInt.toInt (LargeInt.mod (Word16.toLargeInt y, 16))))
fun intrinsic_U32ShiftRight(x : Word32.word, y : Word32.word): Word32.word = Word32.>> (Word32.fromLargeInt (Word32.toLargeInt x), Word.fromInt (LargeInt.toInt (LargeInt.mod (Word32.toLargeInt y, 32))))
fun intrinsic_U64ShiftRight(x : Word64.word, y : Word64.word): Word64.word = Word64.>> (Word64.fromLargeInt (Word64.toLargeInt x), Word.fromInt (LargeInt.toInt (LargeInt.mod (Word64.toLargeInt y, 64))))
fun intrinsic_I8Ctpop(x : Int8.int): Int8.int = Int8.fromLarge (Word8.toLargeIntX (Word8.fromLargeInt (Int.toLarge (popcount64 (Word64.fromLarge (Word8.toLarge (Word8.fromLargeInt (Int8.toLarge x))))))))
fun intrinsic_I16Ctpop(x : Int16.int): Int16.int = Int16.fromLarge (Word16.toLargeIntX (Word16.fromLargeInt (Int.toLarge (popcount64 (Word64.fromLarge (Word16.toLarge (Word16.fromLargeInt (Int16.toLarge x))))))))
fun intrinsic_I32Ctpop(x : Int32.int): Int32.int = Int32.fromLarge (Word32.toLargeIntX (Word32.fromLargeInt (Int.toLarge (popcount64 (Word64.fromLarge (Word32.toLarge (Word32.fromLargeInt (Int32.toLarge x))))))))
fun intrinsic_I64Ctpop(x : Int.int): Int.int = Word64.toIntX (Word64.fromLargeInt (Int.toLarge (popcount64 (Word64.fromLarge (Word64.toLarge (Word64.fromLargeInt (Int.toLarge x)))))))
fun intrinsic_U8Ctpop(x : char): char = chr (Word8.toInt (Word8.fromLargeInt (Int.toLarge (popcount64 (Word64.fromLarge (Word8.toLarge (Word8.fromLargeInt (Int.toLarge (ord x)))))))))
fun intrinsic_U16Ctpop(x : Word16.word): Word16.word = Word16.fromLargeInt (Int.toLarge (popcount64 (Word64.fromLarge (Word16.toLarge (Word16.fromLargeInt (Word16.toLargeInt x))))))
fun intrinsic_U32Ctpop(x : Word32.word): Word32.word = Word32.fromLargeInt (Int.toLarge (popcount64 (Word64.fromLarge (Word32.toLarge (Word32.fromLargeInt (Word32.toLargeInt x))))))
fun intrinsic_U64Ctpop(x : Word64.word): Word64.word = Word64.fromLargeInt (Int.toLarge (popcount64 (Word64.fromLarge (Word64.toLarge (Word64.fromLargeInt (Word64.toLargeInt x))))))
fun intrinsic_I8Ctlz(x : Int8.int): Int8.int = Int8.fromLarge (Word8.toLargeIntX (Word8.fromLargeInt (Int.toLarge (clz64 (Word64.fromLarge (Word8.toLarge (Word8.fromLargeInt (Int8.toLarge x)))) - 56))))
fun intrinsic_I16Ctlz(x : Int16.int): Int16.int = Int16.fromLarge (Word16.toLargeIntX (Word16.fromLargeInt (Int.toLarge (clz64 (Word64.fromLarge (Word16.toLarge (Word16.fromLargeInt (Int16.toLarge x)))) - 48))))
fun intrinsic_I32Ctlz(x : Int32.int): Int32.int = Int32.fromLarge (Word32.toLargeIntX (Word32.fromLargeInt (Int.toLarge (clz64 (Word64.fromLarge (Word32.toLarge (Word32.fromLargeInt (Int32.toLarge x)))) - 32))))
fun intrinsic_I64Ctlz(x : Int.int): Int.int = Word64.toIntX (Word64.fromLargeInt (Int.toLarge (clz64 (Word64.fromLarge (Word64.toLarge (Word64.fromLargeInt (Int.toLarge x)))) - 0)))
fun intrinsic_U8Ctlz(x : char): char = chr (Word8.toInt (Word8.fromLargeInt (Int.toLarge (clz64 (Word64.fromLarge (Word8.toLarge (Word8.fromLargeInt (Int.toLarge (ord x))))) - 56))))
fun intrinsic_U16Ctlz(x : Word16.word): Word16.word = Word16.fromLargeInt (Int.toLarge (clz64 (Word64.fromLarge (Word16.toLarge (Word16.fromLargeInt (Word16.toLargeInt x)))) - 48))
fun intrinsic_U32Ctlz(x : Word32.word): Word32.word = Word32.fromLargeInt (Int.toLarge (clz64 (Word64.fromLarge (Word32.toLarge (Word32.fromLargeInt (Word32.toLargeInt x)))) - 32))
fun intrinsic_U64Ctlz(x : Word64.word): Word64.word = Word64.fromLargeInt (Int.toLarge (clz64 (Word64.fromLarge (Word64.toLarge (Word64.fromLargeInt (Word64.toLargeInt x)))) - 0))
fun intrinsic_I8Cttz(x : Int8.int): Int8.int = Int8.fromLarge (Word8.toLargeIntX (Word8.fromLargeInt (Int.toLarge (Int.min (ctz64 (Word64.fromLarge (Word8.toLarge (Word8.fromLargeInt (Int8.toLarge x)))), 8)))))
fun intrinsic_I16Cttz(x : Int16.int): Int16.int = Int16.fromLarge (Word16.toLargeIntX (Word16.fromLargeInt (Int.toLarge (Int.min (ctz64 (Word64.fromLarge (Word16.toLarge (Word16.fromLargeInt (Int16.toLarge x)))), 16)))))
fun intrinsic_I32Cttz(x : Int32.int): Int32.int = Int32.fromLarge (Word32.toLargeIntX (Word32.fromLargeInt (Int.toLarge (Int.min (ctz64 (Word64.fromLarge (Word32.toLarge (Word32.fromLargeInt (Int32.toLarge x)))), 32)))))
fun intrinsic_I64Cttz(x : Int.int): Int.int = Word64.toIntX (Word64.fromLargeInt (Int.toLarge (Int.min (ctz64 (Word64.fromLarge (Word64.toLarge (Word64.fromLargeInt (Int.toLarge x)))), 64))))
fun intrinsic_U8Cttz(x : char): char = chr (Word8.toInt (Word8.fromLargeInt (Int.toLarge (Int.min (ctz64 (Word64.fromLarge (Word8.toLarge (Word8.fromLargeInt (Int.toLarge (ord x))))), 8)))))
fun intrinsic_U16Cttz(x : Word16.word): Word16.word = Word16.fromLargeInt (Int.toLarge (Int.min (ctz64 (Word64.fromLarge (Word16.toLarge (Word16.fromLargeInt (Word16.toLargeInt x)))), 16)))
fun intrinsic_U32Cttz(x : Word32.word): Word32.word = Word32.fromLargeInt (Int.toLarge (Int.min (ctz64 (Word64.fromLarge (Word32.toLarge (Word32.fromLargeInt (Word32.toLargeInt x)))), 32)))
fun intrinsic_U64Cttz(x : Word64.word): Word64.word = Word64.fromLargeInt (Int.toLarge (Int.min (ctz64 (Word64.fromLarge (Word64.toLarge (Word64.fromLargeInt (Word64.toLargeInt x)))), 64)))
fun intrinsic_I8ToI16(x : Int8.int): Int16.int = Int16.fromLarge (Word16.toLargeIntX (Word16.fromLargeInt (Int8.toLarge x)))
fun intrinsic_I8ToI32(x : Int8.int): Int32.int = Int32.fromLarge (Word32.toLargeIntX (Word32.fromLargeInt (Int8.toLarge x)))
fun intrinsic_I8ToI64(x : Int8.int): Int.int = Word64.toIntX (Word64.fromLargeInt (Int8.toLarge x))
fun intrinsic_I8ToU8(x : Int8.int): char = chr (Word8.toInt (Word8.fromLargeInt (Int8.toLarge x)))
fun intrinsic_I8ToU16(x : Int8.int): Word16.word = Word16.fromLargeInt (Int8.toLarge x)
fun intrinsic_I8ToU32(x : Int8.int): Word32.word = Word32.fromLargeInt (Int8.toLarge x)
fun intrinsic_I8ToU64(x : Int8.int): Word64.word = Word64.fromLargeInt (Int8.toLarge x)
fun intrinsic_I8ToF32(x : Int8.int): Real32.real = Real32.fromLargeInt (Int8.toLarge x)
fun intrinsic_I8ToF64(x : Int8.int): real = Real.fromLargeInt (Int8.toLarge x)
fun intrinsic_I16ToI8(x : Int16.int): Int8.int = Int8.fromLarge (Word8.toLargeIntX (Word8.fromLargeInt (Int16.toLarge x)))
fun intrinsic_I16ToI32(x : Int16.int): Int32.int = Int32.fromLarge (Word32.toLargeIntX (Word32.fromLargeInt (Int16.toLarge x)))
fun intrinsic_I16ToI64(x : Int16.int): Int.int = Word64.toIntX (Word64.fromLargeInt (Int16.toLarge x))
fun intrinsic_I16ToU8(x : Int16.int): char = chr (Word8.toInt (Word8.fromLargeInt (Int16.toLarge x)))
fun intrinsic_I16ToU16(x : Int16.int): Word16.word = Word16.fromLargeInt (Int16.toLarge x)
fun intrinsic_I16ToU32(x : Int16.int): Word32.word = Word32.fromLargeInt (Int16.toLarge x)
fun intrinsic_I16ToU64(x : Int16.int): Word64.word = Word64.fromLargeInt (Int16.toLarge x)
fun intrinsic_I16ToF32(x : Int16.int): Real32.real = Real32.fromLargeInt (Int16.toLarge x)
fun intrinsic_I16ToF64(x : Int16.int): real = Real.fromLargeInt (Int16.toLarge x)
fun intrinsic_I32ToI8(x : Int32.int): Int8.int = Int8.fromLarge (Word8.toLargeIntX (Word8.fromLargeInt (Int32.toLarge x)))
fun intrinsic_I32ToI16(x : Int32.int): Int16.int = Int16.fromLarge (Word16.toLargeIntX (Word16.fromLargeInt (Int32.toLarge x)))
fun intrinsic_I32ToI64(x : Int32.int): Int.int = Word64.toIntX (Word64.fromLargeInt (Int32.toLarge x))
fun intrinsic_I32ToU8(x : Int32.int): char = chr (Word8.toInt (Word8.fromLargeInt (Int32.toLarge x)))
fun intrinsic_I32ToU16(x : Int32.int): Word16.word = Word16.fromLargeInt (Int32.toLarge x)
fun intrinsic_I32ToU32(x : Int32.int): Word32.word = Word32.fromLargeInt (Int32.toLarge x)
fun intrinsic_I32ToU64(x : Int32.int): Word64.word = Word64.fromLargeInt (Int32.toLarge x)
fun intrinsic_I32ToF32(x : Int32.int): Real32.real = Real32.fromLargeInt (Int32.toLarge x)
fun intrinsic_I32ToF64(x : Int32.int): real = Real.fromLargeInt (Int32.toLarge x)
fun intrinsic_I64ToI8(x : Int.int): Int8.int = Int8.fromLarge (Word8.toLargeIntX (Word8.fromLargeInt (Int.toLarge x)))
fun intrinsic_I64ToI16(x : Int.int): Int16.int = Int16.fromLarge (Word16.toLargeIntX (Word16.fromLargeInt (Int.toLarge x)))
fun intrinsic_I64ToI32(x : Int.int): Int32.int = Int32.fromLarge (Word32.toLargeIntX (Word32.fromLargeInt (Int.toLarge x)))
fun intrinsic_I64ToU8(x : Int.int): char = chr (Word8.toInt (Word8.fromLargeInt (Int.toLarge x)))
fun intrinsic_I64ToU16(x : Int.int): Word16.word = Word16.fromLargeInt (Int.toLarge x)
fun intrinsic_I64ToU32(x : Int.int): Word32.word = Word32.fromLargeInt (Int.toLarge x)
fun intrinsic_I64ToU64(x : Int.int): Word64.word = Word64.fromLargeInt (Int.toLarge x)
fun intrinsic_I64ToF32(x : Int.int): Real32.real = Real32.fromLargeInt (Int.toLarge x)
fun intrinsic_I64ToF64(x : Int.int): real = Real.fromLargeInt (Int.toLarge x)
fun intrinsic_U8ToI8(x : char): Int8.int = Int8.fromLarge (Word8.toLargeIntX (Word8.fromLargeInt (Int.toLarge (ord x))))
fun intrinsic_U8ToI16(x : char): Int16.int = Int16.fromLarge (Word16.toLargeIntX (Word16.fromLargeInt (Int.toLarge (ord x))))
fun intrinsic_U8ToI32(x : char): Int32.int = Int32.fromLarge (Word32.toLargeIntX (Word32.fromLargeInt (Int.toLarge (ord x))))
fun intrinsic_U8ToI64(x : char): Int.int = Word64.toIntX (Word64.fromLargeInt (Int.toLarge (ord x)))
fun intrinsic_U8ToU16(x : char): Word16.word = Word16.fromLargeInt (Int.toLarge (ord x))
fun intrinsic_U8ToU32(x : char): Word32.word = Word32.fromLargeInt (Int.toLarge (ord x))
fun intrinsic_U8ToU64(x : char): Word64.word = Word64.fromLargeInt (Int.toLarge (ord x))
fun intrinsic_U8ToF32(x : char): Real32.real = Real32.fromLargeInt (Int.toLarge (ord x))
fun intrinsic_U8ToF64(x : char): real = Real.fromLargeInt (Int.toLarge (ord x))
fun intrinsic_U16ToI8(x : Word16.word): Int8.int = Int8.fromLarge (Word8.toLargeIntX (Word8.fromLargeInt (Word16.toLargeInt x)))
fun intrinsic_U16ToI16(x : Word16.word): Int16.int = Int16.fromLarge (Word16.toLargeIntX (Word16.fromLargeInt (Word16.toLargeInt x)))
fun intrinsic_U16ToI32(x : Word16.word): Int32.int = Int32.fromLarge (Word32.toLargeIntX (Word32.fromLargeInt (Word16.toLargeInt x)))
fun intrinsic_U16ToI64(x : Word16.word): Int.int = Word64.toIntX (Word64.fromLargeInt (Word16.toLargeInt x))
fun intrinsic_U16ToU8(x : Word16.word): char = chr (Word8.toInt (Word8.fromLargeInt (Word16.toLargeInt x)))
fun intrinsic_U16ToU32(x : Word16.word): Word32.word = Word32.fromLargeInt (Word16.toLargeInt x)
fun intrinsic_U16ToU64(x : Word16.word): Word64.word = Word64.fromLargeInt (Word16.toLargeInt x)
fun intrinsic_U16ToF32(x : Word16.word): Real32.real = Real32.fromLargeInt (Word16.toLargeInt x)
fun intrinsic_U16ToF64(x : Word16.word): real = Real.fromLargeInt (Word16.toLargeInt x)
fun intrinsic_U32ToI8(x : Word32.word): Int8.int = Int8.fromLarge (Word8.toLargeIntX (Word8.fromLargeInt (Word32.toLargeInt x)))
fun intrinsic_U32ToI16(x : Word32.word): Int16.int = Int16.fromLarge (Word16.toLargeIntX (Word16.fromLargeInt (Word32.toLargeInt x)))
fun intrinsic_U32ToI32(x : Word32.word): Int32.int = Int32.fromLarge (Word32.toLargeIntX (Word32.fromLargeInt (Word32.toLargeInt x)))
fun intrinsic_U32ToI64(x : Word32.word): Int.int = Word64.toIntX (Word64.fromLargeInt (Word32.toLargeInt x))
fun intrinsic_U32ToU8(x : Word32.word): char = chr (Word8.toInt (Word8.fromLargeInt (Word32.toLargeInt x)))
fun intrinsic_U32ToU16(x : Word32.word): Word16.word = Word16.fromLargeInt (Word32.toLargeInt x)
fun intrinsic_U32ToU64(x : Word32.word): Word64.word = Word64.fromLargeInt (Word32.toLargeInt x)
fun intrinsic_U32ToF32(x : Word32.word): Real32.real = Real32.fromLargeInt (Word32.toLargeInt x)
fun intrinsic_U32ToF64(x : Word32.word): real = Real.fromLargeInt (Word32.toLargeInt x)
fun intrinsic_U64ToI8(x : Word64.word): Int8.int = Int8.fromLarge (Word8.toLargeIntX (Word8.fromLargeInt (Word64.toLargeInt x)))
fun intrinsic_U64ToI16(x : Word64.word): Int16.int = Int16.fromLarge (Word16.toLargeIntX (Word16.fromLargeInt (Word64.toLargeInt x)))
fun intrinsic_U64ToI32(x : Word64.word): Int32.int = Int32.fromLarge (Word32.toLargeIntX (Word32.fromLargeInt (Word64.toLargeInt x)))
fun intrinsic_U64ToI64(x : Word64.word): Int.int = Word64.toIntX (Word64.fromLargeInt (Word64.toLargeInt x))
fun intrinsic_U64ToU8(x : Word64.word): char = chr (Word8.toInt (Word8.fromLargeInt (Word64.toLargeInt x)))
fun intrinsic_U64ToU16(x : Word64.word): Word16.word = Word16.fromLargeInt (Word64.toLargeInt x)
fun intrinsic_U64ToU32(x : Word64.word): Word32.word = Word32.fromLargeInt (Word64.toLargeInt x)
fun intrinsic_U64ToF32(x : Word64.word): Real32.real = Real32.fromLargeInt (Word64.toLargeInt x)
fun intrinsic_U64ToF64(x : Word64.word): real = Real.fromLargeInt (Word64.toLargeInt x)
fun intrinsic_F32ToI8(x : Real32.real): Int8.int = if Real32.isNan x then Int8.fromLarge (Word8.toLargeIntX (Word8.fromLargeInt (0))) else if x <= ~128.0 then Int8.fromLarge (Word8.toLargeIntX (Word8.fromLargeInt (~128))) else if x >= 127.0 then Int8.fromLarge (Word8.toLargeIntX (Word8.fromLargeInt (127))) else Int8.fromLarge (Word8.toLargeIntX (Word8.fromLargeInt (Real32.toLargeInt IEEEReal.TO_ZERO x)))
fun intrinsic_F32ToI16(x : Real32.real): Int16.int = if Real32.isNan x then Int16.fromLarge (Word16.toLargeIntX (Word16.fromLargeInt (0))) else if x <= ~32768.0 then Int16.fromLarge (Word16.toLargeIntX (Word16.fromLargeInt (~32768))) else if x >= 32767.0 then Int16.fromLarge (Word16.toLargeIntX (Word16.fromLargeInt (32767))) else Int16.fromLarge (Word16.toLargeIntX (Word16.fromLargeInt (Real32.toLargeInt IEEEReal.TO_ZERO x)))
fun intrinsic_F32ToI32(x : Real32.real): Int32.int = if Real32.isNan x then Int32.fromLarge (Word32.toLargeIntX (Word32.fromLargeInt (0))) else if x <= ~2147483648.0 then Int32.fromLarge (Word32.toLargeIntX (Word32.fromLargeInt (~2147483648))) else if x >= 2147483647.0 then Int32.fromLarge (Word32.toLargeIntX (Word32.fromLargeInt (2147483647))) else Int32.fromLarge (Word32.toLargeIntX (Word32.fromLargeInt (Real32.toLargeInt IEEEReal.TO_ZERO x)))
fun intrinsic_F32ToI64(x : Real32.real): Int.int = if Real32.isNan x then Word64.toIntX (Word64.fromLargeInt (0)) else if x <= ~9223372036854775808.0 then Word64.toIntX (Word64.fromLargeInt (~9223372036854775808)) else if x >= 9223372036854775807.0 then Word64.toIntX (Word64.fromLargeInt (9223372036854775807)) else Word64.toIntX (Word64.fromLargeInt (Real32.toLargeInt IEEEReal.TO_ZERO x))
fun intrinsic_F32ToU8(x : Real32.real): char = if Real32.isNan x then chr (Word8.toInt (Word8.fromLargeInt (0))) else if x <= 0.0 then chr (Word8.toInt (Word8.fromLargeInt (0))) else if x >= 255.0 then chr (Word8.toInt (Word8.fromLargeInt (255))) else chr (Word8.toInt (Word8.fromLargeInt (Real32.toLargeInt IEEEReal.TO_ZERO x)))
fun intrinsic_F32ToU16(x : Real32.real): Word16.word = if Real32.isNan x then Word16.fromLargeInt (0) else if x <= 0.0 then Word16.fromLargeInt (0) else if x >= 65535.0 then Word16.fromLargeInt (65535) else Word16.fromLargeInt (Real32.toLargeInt IEEEReal.TO_ZERO x)
fun intrinsic_F32ToU32(x : Real32.real): Word32.word = if Real32.isNan x then Word32.fromLargeInt (0) else if x <= 0.0 then Word32.fromLargeInt (0) else if x >= 4294967295.0 then Word32.fromLargeInt (4294967295) else Word32.fromLargeInt (Real32.toLargeInt IEEEReal.TO_ZERO x)
fun intrinsic_F32ToU64(x : Real32.real): Word64.word = if Real32.isNan x then Word64.fromLargeInt (0) else if x <= 0.0 then Word64.fromLargeInt (0) else if x >= 18446744073709551615.0 then Word64.fromLargeInt (18446744073709551615) else Word64.fromLargeInt (Real32.toLargeInt IEEEReal.TO_ZERO x)
fun intrinsic_F32ToF64(x : Real32.real): real = Real32.toLarge x
fun intrinsic_F64ToI8(x : real): Int8.int = if Real.isNan x then Int8.fromLarge (Word8.toLargeIntX (Word8.fromLargeInt (0))) else if x <= ~128.0 then Int8.fromLarge (Word8.toLargeIntX (Word8.fromLargeInt (~128))) else if x >= 127.0 then Int8.fromLarge (Word8.toLargeIntX (Word8.fromLargeInt (127))) else Int8.fromLarge (Word8.toLargeIntX (Word8.fromLargeInt (Real.toLargeInt IEEEReal.TO_ZERO x)))
fun intrinsic_F64ToI16(x : real): Int16.int = if Real.isNan x then Int16.fromLarge (Word16.toLargeIntX (Word16.fromLargeInt (0))) else if x <= ~32768.0 then Int16.fromLarge (Word16.toLargeIntX (Word16.fromLargeInt (~32768))) else if x >= 32767.0 then Int16.fromLarge (Word16.toLargeIntX (Word16.fromLargeInt (32767))) else Int16.fromLarge (Word16.toLargeIntX (Word16.fromLargeInt (Real.toLargeInt IEEEReal.TO_ZERO x)))
fun intrinsic_F64ToI32(x : real): Int32.int = if Real.isNan x then Int32.fromLarge (Word32.toLargeIntX (Word32.fromLargeInt (0))) else if x <= ~2147483648.0 then Int32.fromLarge (Word32.toLargeIntX (Word32.fromLargeInt (~2147483648))) else if x >= 2147483647.0 then Int32.fromLarge (Word32.toLargeIntX (Word32.fromLargeInt (2147483647))) else Int32.fromLarge (Word32.toLargeIntX (Word32.fromLargeInt (Real.toLargeInt IEEEReal.TO_ZERO x)))
fun intrinsic_F64ToI64(x : real): Int.int = if Real.isNan x then Word64.toIntX (Word64.fromLargeInt (0)) else if x <= ~9223372036854775808.0 then Word64.toIntX (Word64.fromLargeInt (~9223372036854775808)) else if x >= 9223372036854775807.0 then Word64.toIntX (Word64.fromLargeInt (9223372036854775807)) else Word64.toIntX (Word64.fromLargeInt (Real.toLargeInt IEEEReal.TO_ZERO x))
fun intrinsic_F64ToU8(x : real): char = if Real.isNan x then chr (Word8.toInt (Word8.fromLargeInt (0))) else if x <= 0.0 then chr (Word8.toInt (Word8.fromLargeInt (0))) else if x >= 255.0 then chr (Word8.toInt (Word8.fromLargeInt (255))) else chr (Word8.toInt (Word8.fromLargeInt (Real.toLargeInt IEEEReal.TO_ZERO x)))
fun intrinsic_F64ToU16(x : real): Word16.word = if Real.isNan x then Word16.fromLargeInt (0) else if x <= 0.0 then Word16.fromLargeInt (0) else if x >= 65535.0 then Word16.fromLargeInt (65535) else Word16.fromLargeInt (Real.toLargeInt IEEEReal.TO_ZERO x)
fun intrinsic_F64ToU32(x : real): Word32.word = if Real.isNan x then Word32.fromLargeInt (0) else if x <= 0.0 then Word32.fromLargeInt (0) else if x >= 4294967295.0 then Word32.fromLargeInt (4294967295) else Word32.fromLargeInt (Real.toLargeInt IEEEReal.TO_ZERO x)
fun intrinsic_F64ToU64(x : real): Word64.word = if Real.isNan x then Word64.fromLargeInt (0) else if x <= 0.0 then Word64.fromLargeInt (0) else if x >= 18446744073709551615.0 then Word64.fromLargeInt (18446744073709551615) else Word64.fromLargeInt (Real.toLargeInt IEEEReal.TO_ZERO x)
fun intrinsic_F64ToF32(x : real): Real32.real = Real32.fromLarge IEEEReal.TO_NEAREST x


fun intrinsic_get(l : 'a PersistentArray.array, i : Int.int): 'a = PersistentArray.sub (l, i)
fun intrinsic_extract(l : 'a PersistentArray.array, i : Int.int): 'a * ('a -> 'a PersistentArray.array) = (PersistentArray.sub (l, i), fn new => PersistentArray.update (l, i, new))
fun intrinsic_len(l : 'a PersistentArray.array): Int.int = PersistentArray.length l
fun intrinsic_push(l : 'a PersistentArray.array, x : 'a): 'a PersistentArray.array = PersistentArray.append (l, x)
fun intrinsic_pop(l : 'a PersistentArray.array): 'a PersistentArray.array * 'a = PersistentArray.popEnd(l)
fun intrinsic_reserve(l : 'a PersistentArray.array, i : Int.int): 'a PersistentArray.array = l
fun intrinsic_replace(f : 'a -> 'a PersistentArray.array, x : 'a): 'a PersistentArray.array = f x

fun input(()) : char PersistentArray.array = #1 (intrinsic_pop (PersistentArray.fromList (explode (Option.getOpt ((TextIO.inputLine TextIO.stdIn), "\n")))))
fun output(l : char PersistentArray.array) = print (implode (PersistentArray.toList l))
fun panic(l : char PersistentArray.array) = raise Fail (implode (PersistentArray.toList l))
