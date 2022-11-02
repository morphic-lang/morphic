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
fun intrinsic_replace(f : 'a -> 'a PersistentArray.array, x : 'a): 'a PersistentArray.array = f x

fun input(()) : char PersistentArray.array = #1 (intrinsic_pop (PersistentArray.fromList (explode (Option.getOpt ((TextIO.inputLine TextIO.stdIn), "\n")))))
fun output(l : char PersistentArray.array) = print (implode (PersistentArray.toList l))
fun panic(l : char PersistentArray.array) = raise Fail (implode (PersistentArray.toList l))
