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
fun intrinsic_AddInt(x : Int.int, y : Int.int): Int.int = Word64.toIntX (Word64.fromInt x + Word64.fromInt y)
fun intrinsic_SubInt(x : Int.int, y : Int.int): Int.int = Word64.toIntX (Word64.fromInt x - Word64.fromInt y)
fun intrinsic_MulInt(x : Int.int, y : Int.int): Int.int = Word64.toIntX (Word64.fromInt x * Word64.fromInt y)
fun intrinsic_DivInt(x : Int.int, y : Int.int): Int.int = Word64.toIntX (Word64.fromInt x div Word64.fromInt y)
fun intrinsic_NegInt(x : Int.int): Int.int = Word64.toIntX (~ (Word64.fromInt x))
fun intrinsic_EqInt(x : Int.int, y : Int.int): bool = x = y
fun intrinsic_LtInt(x : Int.int, y : Int.int): bool = x < y
fun intrinsic_LteInt(x : Int.int, y : Int.int): bool = x <= y
fun intrinsic_GtInt(x : Int.int, y : Int.int): bool = x > y
fun intrinsic_GteInt(x : Int.int, y : Int.int): bool = x >= y
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
fun intrinsic_ByteToInt(x : char): Int.int = ord x
fun intrinsic_ByteToIntSigned(x : char): Int.int = Word8.toIntX (Word8.fromInt (ord x))
fun intrinsic_IntToByte(x : Int.int): char = chr (Word8.toInt (Word8.fromInt x))
fun intrinsic_IntShiftLeft(x : Int.int, y : Int.int): Int.int = Word64.toIntX (Word64.<< (Word64.fromInt x, Word.fromInt (y mod 64)))
fun intrinsic_IntShiftRight(x : Int.int, y : Int.int): Int.int = Word64.toIntX (Word64.>> (Word64.fromInt x, Word.fromInt (y mod 64)))
fun intrinsic_IntBitAnd(x : Int.int, y : Int.int): Int.int = Word64.toIntX (Word64.andb (Word64.fromInt x, Word64.fromInt y))
fun intrinsic_IntBitOr(x : Int.int, y : Int.int): Int.int = Word64.toIntX (Word64.orb (Word64.fromInt x, Word64.fromInt y))
fun intrinsic_IntBitXor(x : Int.int, y : Int.int): Int.int = Word64.toIntX (Word64.xorb (Word64.fromInt x, Word64.fromInt y))
fun intrinsic_IntCtpop(x : Int.int): Int.int = 
    let
        fun count_bits(0w0 : Word64.word) = 0
          | count_bits(w) = Word64.toInt(Word64.andb(w, 0w1)) + count_bits(Word64.>>(w, 0w1))
    in
        count_bits(Word64.fromInt x)
    end

fun intrinsic_IntCtlz(x : Int.int): Int.int =
    let 
        fun count_leading_zeros(w : Word64.word, acc : int) =
            if w = 0w0 then
                64
            else if Word64.andb(Word64.>>(w, 0w63), 0w1) = 0w1 then
                acc
            else
                count_leading_zeros(Word64.<<(w, 0w1), acc + 1)
    in
        count_leading_zeros(Word64.fromInt x, 0)
    end

fun intrinsic_IntCttz(x : Int.int): Int.int =
    let
        fun count_trailing_zeros(w : Word64.word, acc : int) =
            if w = 0w0 then
                64
            else if Word64.andb(w, 0w1) = 0w1 then
                acc
            else
                count_trailing_zeros(Word64.>>(w, 0w1), acc + 1)
    in
        count_trailing_zeros(Word64.fromInt x, 0)
    end


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
