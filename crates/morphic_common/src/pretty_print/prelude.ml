let intrinsic_AddByte ((x, y) : char * char): char = Char.chr (((Char.code x + Char.code y) mod 256 + 256) mod 256)
let intrinsic_SubByte ((x, y) : char * char): char = Char.chr (((Char.code x - Char.code y) mod 256 + 256) mod 256)
let intrinsic_MulByte ((x, y) : char * char): char = Char.chr (((Char.code x * Char.code y) mod 256 + 256) mod 256)
let intrinsic_DivByte ((x, y) : char * char): char = Char.chr (((Char.code x / Char.code y) mod 256 + 256) mod 256)
let intrinsic_NegByte (x: char) = Char.chr (((-Char.code x) mod 256 + 256) mod 256)
let intrinsic_EqByte ((x, y) : char * char): bool = x = y
let intrinsic_LtByte ((x, y) : char * char): bool = x < y
let intrinsic_LteByte ((x, y) : char * char): bool = x <= y
let intrinsic_GtByte ((x, y) : char * char): bool = x > y
let intrinsic_GteByte ((x, y) : char * char): bool = x >= y
let intrinsic_AddInt ((x, y) : int64 * int64): int64 = Int64.add x y
let intrinsic_SubInt ((x, y) : int64 * int64): int64 = Int64.sub x y
let intrinsic_MulInt ((x, y) : int64 * int64): int64 = Int64.mul x y
let intrinsic_DivInt ((x, y) : int64 * int64): int64 = Int64.div x y
let intrinsic_NegInt (x : int64) : int64 = Int64.neg x
let intrinsic_EqInt ((x, y) : int64 * int64): bool = x = y
let intrinsic_LtInt ((x, y) : int64 * int64): bool = x < y
let intrinsic_LteInt ((x, y) : int64 * int64): bool = x <= y
let intrinsic_GtInt ((x, y) : int64 * int64): bool = x > y
let intrinsic_GteInt ((x, y) : int64 * int64): bool = x >= y
let intrinsic_AddFloat ((x, y) : float * float): float = x +. y
let intrinsic_SubFloat ((x, y) : float * float): float = x -. y
let intrinsic_MulFloat ((x, y) : float * float): float = x *. y
let intrinsic_DivFloat ((x, y) : float * float): float = x /. y
let intrinsic_NegFloat (x : float) : float = -.x
let intrinsic_EqFloat ((x, y) : float * float): bool = x = y
let intrinsic_LtFloat ((x, y) : float * float): bool = x < y
let intrinsic_LteFloat ((x, y) : float * float): bool = x <= y
let intrinsic_GtFloat ((x, y) : float * float): bool = x > y
let intrinsic_GteFloat ((x, y) : float * float): bool = x >= y
let intrinsic_Not (x : bool) : bool = not x
let intrinsic_ByteToInt (x : char) : int64 = Int64.of_int (Char.code x)
let intrinsic_ByteToIntSigned (x : char) : int64 = Int64.sub (Int64.logxor (Int64.of_int (Char.code x)) 0x80L) 0x80L
let intrinsic_IntToByte (x : int64) : char = Char.chr (Int64.to_int (Int64.rem (Int64.add (Int64.rem x 256L) 256L) 256L))
let intrinsic_IntShiftLeft ((x, y) : int64 * int64): int64 = Int64.shift_left x (Int64.to_int y)
let intrinsic_IntShiftRight ((x, y) : int64 * int64): int64 = Int64.shift_right_logical x (Int64.to_int y)
let intrinsic_IntBitAnd ((x, y) : int64 * int64): int64 = Int64.logand x y
let intrinsic_IntBitOr ((x, y) : int64 * int64): int64 = Int64.logor x y
let intrinsic_IntBitXor ((x, y) : int64 * int64): int64 = Int64.logxor x y
let intrinsic_IntCtpop (x : int64) : int64 =
    let rec count_bits n acc =
        if n >= 64 then acc
        else if Int64.logand (Int64.shift_right_logical x n) 1L = 1L then
            count_bits (n + 1) (acc + 1)
        else
            count_bits (n + 1) acc
    in Int64.of_int (count_bits 0 0)
let intrinsic_IntCtlz (x : int64) : int64 = 
    let rec count_leading n =
        if n >= 64 then 64
        else if Int64.logand (Int64.shift_right_logical x (63 - n)) 1L <> 0L then n
        else count_leading (n + 1)
    in Int64.of_int (count_leading 0)
let intrinsic_IntCttz (x : int64) : int64 = 
    let rec count_trailing n =
        if n >= 64 then 64
        else if Int64.logand x (Int64.shift_left 1L n) <> 0L then n
        else count_trailing (n + 1)
    in Int64.of_int (count_trailing 0)


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
