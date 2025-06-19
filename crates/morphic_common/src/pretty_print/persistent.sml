(* The following persistent array implementation is the concatination of a *)
(* bunch of files of the following github project with unused code removed *)
(* https://github.com/cannam/sml-trie/commit/aa7ef231840f55692f5f44ec785392854382acbe *)

(*
    Copyright 2015-2021 Chris Cannam.

    Permission is hereby granted, free of charge, to any person
    obtaining a copy of this software and associated documentation
    files (the "Software"), to deal in the Software without
    restriction, including without limitation the rights to use, copy,
    modify, merge, publish, distribute, sublicense, and/or sell copies
    of the Software, and to permit persons to whom the Software is
    furnished to do so, subject to the following conditions:

    The above copyright notice and this permission notice shall be
    included in all copies or substantial portions of the Software.

    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
    EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
    MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR
    ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF
    CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
    WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

    Except as contained in this notice, the names of Chris Cannam and
    Particular Programs Ltd shall not be used in advertising or
    otherwise to promote the sale, use or other dealings in this
    Software without prior written authorization.
*)

(* Copyright 2015-2021 Chris Cannam.
   MIT/X11 licence. See the file COPYING for details. *)

signature TRIE_MAP = sig

    type 'a trie
    type key

    (** Empty trie *)
    val empty : 'a trie

    (** Test whether a trie is empty *)
    val isEmpty : 'a trie -> bool

    (** Insert a key-value pair, returning a new trie. If the key is
        already present, its value will be updated in the new trie *)
    val insert : 'a trie * key * 'a -> 'a trie

    (** Return the trie with the given key removed. If the key is
        not present, the returned trie will be unchanged *)
    val remove : 'a trie * key -> 'a trie

    (** Look for a key and return its corresponding value, or NONE if
        the key is not present in the trie *)
    val find : 'a trie * key -> 'a option

    (** Look for a key and return its corresponding value, raising
        Subscript if the key is not present in the trie *)
    val lookup : 'a trie * key -> 'a

    (** Fold over all the values in the trie, in reverse of sort order
        by key *)
    val foldr : ('a * 'b -> 'b) -> 'b -> 'a trie -> 'b

end

(* Copyright 2015-2021 Chris Cannam.
   MIT/X11 licence. See the file COPYING for details. *)

(** Signature for the map used within a trie node to store branching
    information.
 *)
signature TRIE_NODE_MAP = sig
    eqtype key
    type 'a map
    val new : unit -> 'a map
    val isEmpty : 'a map -> bool
    val find : 'a map * key -> 'a option
    val foldr : ('a * 'b -> 'b) -> 'b -> 'a map -> 'b
    val alter : 'a map * key * ('a option -> 'a option) -> 'a map
    val remove : 'a map * key -> 'a map
end

signature TRIE_KEY = sig
    eqtype element
    type key
    val isEmpty : key -> bool
    val head : key -> element
    val tail : key -> key
    val equal : key * key -> bool
end

signature TRIE_MAP_FN_ARG = sig
    eqtype element
    type key
    structure M : TRIE_NODE_MAP where type key = element
    structure K : TRIE_KEY where type element = element where type key = key
end

functor TrieMapFn (A : TRIE_MAP_FN_ARG)
	:> TRIE_MAP
	       where type key = A.K.key = struct

    structure M = A.M
    structure K = A.K

    type element = K.element
    type key = K.key
    type pattern = element option list
    type range = key option * key option

    datatype 'a node = LEAF of 'a
                     | TWIG of key * 'a (* key nonempty, else it's a leaf *)
                     | BRANCH of 'a option * 'a node M.map

    datatype 'a trie = EMPTY
                     | POPULATED of 'a node

    val empty = EMPTY

    fun isEmpty EMPTY = true
      | isEmpty _ = false

    fun newBranch opt = BRANCH (opt, M.new ())

    fun isEmptyBranch (BRANCH (NONE, m)) = M.isEmpty m
      | isEmptyBranch _ = false

    fun alter' (n, xx, f : 'a option -> 'a option) =
        if K.isEmpty xx
        then
            case n of
                LEAF existing =>
                (case f (SOME existing) of
                     NONE => newBranch NONE
                   | SOME replacement => LEAF replacement)
              | TWIG (kk, unrelated) =>
                (case f NONE of
                     NONE => TWIG (kk, unrelated)
                   | SOME new =>
                     (* switch to inserting the existing item back into
                        a branch built on the new one *)
                     alter' (newBranch (SOME new), kk, fn _ => SOME unrelated))
              | BRANCH (iopt, m) => BRANCH (f iopt, m)
        else (* xx is nonempty, so we are not at our leaf yet *)
            case n of
                LEAF unrelated =>
                (case f NONE of
                     NONE => LEAF unrelated
                   | SOME new =>
                     alter' (newBranch (SOME unrelated), xx, fn _ => SOME new))
              | TWIG (kk, existing) =>
                (if K.equal (kk, xx)
                 then case f (SOME existing) of
                          NONE => newBranch NONE
                        | SOME replacement => TWIG (kk, replacement)
                 else case f NONE of
                          NONE => TWIG (kk, existing)
                        | SOME new =>
                          if K.head kk = K.head xx (* e.g. XDEF next to XABC *)
                          then let val nsub = alter' (newBranch NONE,
                                                      K.tail xx,
                                                      fn _ => SOME new)
                                   (* reinsert existing into new: *)
                                   val nsub = alter' (nsub,
                                                      K.tail kk,
                                                      fn _ => SOME existing)
                               in
                                   BRANCH (NONE,
                                           M.alter (M.new (), K.head xx,
                                                    fn _ => SOME nsub))
                               end
                          else (* e.g. CDEF next to GHIJ, both known nonempty *)
                              alter' (alter' (newBranch NONE, kk,
                                              fn _ => SOME existing),
                                      xx, fn _ => SOME new))
              | BRANCH (iopt, m) =>
                BRANCH (iopt,
                        M.alter
                            (m, K.head xx,
                             fn NONE =>
                                (case f NONE of
                                     NONE => NONE
                                   | SOME new =>
                                     SOME (let val xs = K.tail xx
                                           in
                                               if K.isEmpty xs
                                               then LEAF new
                                               else TWIG (xs, new)
                                           end))
                             | SOME nsub =>
                               let val nsub' = alter' (nsub, K.tail xx, f)
                               in
                                   if isEmptyBranch nsub'
                                   then NONE
                                   else SOME nsub'
                               end))

    fun alter (n, xx, f) =
        let val n' = alter' (case n of
                                 EMPTY => newBranch NONE
                               | POPULATED n => n,
                             xx, f)
        in
            if isEmptyBranch n'
            then EMPTY
            else
                POPULATED n'
        end

    fun insert (nopt, xx, v) =
        alter (nopt, xx, fn _ => SOME v)

    fun remove (nopt, xx) =
        alter (nopt, xx, fn _ => NONE)

    fun find' (n, xx) =
        if K.isEmpty xx
        then
            case n of
                LEAF item => SOME item
              | TWIG (kk, item) => NONE  (* kk should always be nonempty *)
              | BRANCH (iopt, m) => iopt
        else
            case n of
                LEAF _ => NONE
              | TWIG (kk, item) => (if K.equal (kk, xx)
                                    then SOME item
                                    else NONE)
              | BRANCH (_, m) =>
                case M.find (m, K.head xx) of
                    NONE => NONE
                  | SOME nsub => find' (nsub, K.tail xx)

    fun findi (EMPTY, _) = NONE
      | findi (POPULATED n, xx) =
        case find' (n, xx) of
            NONE => NONE
          | SOME v => SOME (xx, v)

    fun find (EMPTY, _) = NONE
      | find (POPULATED n, xx) =
        find' (n, xx)

    (* We use the name rpfx throughout this file to refer to a
       reversed prefix of a key built up using cons as we descend
       through the trie. It can be converted back into a key with
       (K.implode o rev). *)

    fun lookup (t, k) =
        case find (t, k) of
            NONE => raise Subscript
          | SOME v => v

    fun foldrNode f =
        let fun fold' (n, acc) =
                case n of
                    LEAF item => f (item, acc)
                  | TWIG (kk, item) => f (item, acc)
                  | BRANCH (iopt, m) =>
                    let val acc = M.foldr fold' acc m
                    in case iopt of
                           NONE => acc
                         | SOME item => f (item, acc)
                    end
        in
            fold'
        end

    fun foldr (f : 'a * 'b -> 'b) (acc : 'b) (t : 'a trie) : 'b =
        case t of
            EMPTY => acc
          | POPULATED n => foldrNode f (n, acc)

end




(* Copyright 2018 Chris Cannam.
   MIT/X11 licence. See the file COPYING for details. *)

signature BIT_VECTOR = sig
    type vector
    val new : int -> vector
    val length : vector -> int
    val sub : vector * int -> bool
    val update : vector * int * bool -> vector
    val popcount : vector * int -> int
    exception UnsupportedLength
end

structure BitWord32 :> BIT_VECTOR = struct

    local
        fun bitMask i : Word32.word =
            Word32.<< (0w1, Word.andb (Word.fromInt i, 0w31))

        open Word32

        (* 32-bit population-count, Bagwell 2001 *)
        fun pc32 w =
            let open Word32
                val sk5 = 0wx55555555
                val sk3 = 0wx33333333
                val skf0 = 0wxf0f0f0f
                val skff = 0wxff00ff
                val w = w - (andb (>> (w, 0w1), sk5))
                val w = andb (w, sk3) + (andb (>> (w, 0w2), sk3))
                val w = andb (w, skf0) + (andb (>> (w, 0w4), skf0))
                val w = w + >> (w, 0w8)
            in
                andb (w + >> (w, 0w16), 0wx3f)
            end
    in

    type vector = Word32.word
    exception UnsupportedLength

    fun new n = if n = 32
                then Word32.fromInt 0
                else raise UnsupportedLength

    fun length _ = 32

    fun sub (w : Word32.word, i : int) : bool =
        andb (w, bitMask i) <> 0w0

    fun update (w : Word32.word, i : int, b : bool) : Word32.word =
        if b
        then orb (w, bitMask i)
        else andb (w, notb (bitMask i))

    (* return number of 1s in the first i bits of the word *)
    fun popcount (w : Word32.word, i : int) : int =
        Word32.toInt
            (pc32 (if Int.<(i, 32)
                   then andb (w, bitMask i - 0w1)
                   else w))

    end
end

functor BitMappedVectorFn (V : BIT_VECTOR) = struct

    type 'a vector = V.vector * 'a vector

    fun new n : 'a vector =
        (V.new n, Vector.fromList [])

    fun length ((b, _) : 'a vector) : int =
        V.length b

    fun population ((_, v) : 'a vector) : int =
        Vector.length v

    fun isEmpty (vec : 'a vector) : bool =
        population vec = 0

    fun find ((b, v) : 'a vector, i : int) : 'a option =
        if V.sub (b, i)
        then let val ix = V.popcount (b, i)
             in
                 SOME (Vector.sub (v, ix))
             end
        else NONE

    fun sub (vec : 'a vector, i : int) : 'a =
        case find (vec, i) of
            NONE => raise Subscript
          | SOME x => x

    fun alter ((b, v) : 'a vector, i : int, f : 'a option -> 'a option) : 'a vector =
        let val pc = V.popcount (b, i)
        in
            if V.sub (b, i)
            then case f (SOME (Vector.sub (v, pc))) of
                     NONE =>
                     (V.update (b, i, false),
                      Vector.tabulate (Vector.length v - 1,
                                       fn j => if j < pc
                                               then Vector.sub (v, j)
                                               else Vector.sub (v, j + 1)))
                   | SOME x =>
                     (b, Vector.update (v, pc, x))
            else case f NONE of
                     NONE =>
                     (b, v)
                   | SOME x =>
                     (V.update (b, i, true),
                      Vector.tabulate (Vector.length v + 1,
                                       fn j => if j < pc
                                               then Vector.sub (v, j)
                                               else if j > pc
                                               then Vector.sub (v, j - 1)
                                               else x))
        end

    fun update (vec, i, x) =
        alter (vec, i, fn _ => SOME x)

    fun remove (vec, i) =
        alter (vec, i, fn _ => NONE)

    fun foldr (f : ('a * 'b -> 'b))
              (acc : 'b) ((_, v) : 'a vector) : 'b =
        Vector.foldr f acc v

end

structure BitMappedVector32 = BitMappedVectorFn(BitWord32)

(* Copyright 2015-2021 Chris Cannam.
   MIT/X11 licence. See the file COPYING for details. *)

structure Word32NodeMap
          :> TRIE_NODE_MAP
                 where type key = int = struct

    structure V = BitMappedVector32

    type key = int
    type 'a map = 'a V.vector

    open V

    fun new () = V.new 32
    fun update (v, k, f) = V.alter (v, k, fn x => SOME (f x))

end

structure Word32TrieMap
          :> TRIE_MAP
                 where type key = Word32.word = struct

    type key = Word32.word

    structure Key = struct

        (* The 32-bit word key gets split up into 5-bit chunks (and
           one remaining 2-bit chunk). 5 bits represent the range
           0-31, thus fitting neatly in the 32-bit compression bitmap
           we have available through Word32NodeMap. It is coincidence
           that this happens to be the same as the key size *)

        val bitsPerNode = 5    (* This cannot be > 5, since we are using a
                                  32-bit bitmap for 32 slots in our vector *)

        val bitsPerNodeW = Word.fromInt bitsPerNode
        val maskShift = 0w32 - bitsPerNodeW

        type element = int
        type key = Word32.word
        fun isEmpty w = w = Word32.fromInt 0
        fun head w = Word32.toIntX (Word32.>> (w, maskShift))
        fun tail w = Word32.<< (w, bitsPerNodeW)
        fun equal (w, w') = w = w'
    end

    structure T = TrieMapFn
                      (struct
                        structure M = Word32NodeMap
                        structure K = Key
                        type element = K.element
                        type key = K.key
                        end)

    open T

end

structure PersistentArrayImpl = struct

    structure T = Word32TrieMap

    datatype 'a array = A of {
        size : Word32.word,
        trie : 'a T.trie
    }

    val maxLenW =
        (* Should equal Int.maxInt if Int is no more than 32 bits, or
           the max word32 otherwise *)
        let val wordMax = Word32.- (0w0, 0w1)
        in
            case (Int.precision, Int.maxInt) of
                (NONE, _) => wordMax
              | (_, NONE) => wordMax
              | (SOME p, SOME max) => if p <= 32
                                      then Word32.fromInt max
                                      else wordMax
        end

    val maxLen = Word32.toInt maxLenW

    val empty : 'a array = A {
        size = 0w0,
        trie = T.empty
    }

    fun length (A { size, trie }) =
        Word32.toInt size

    fun append (A { size, trie }, x) =
        let val _ = if size = maxLenW then raise Size else ()
            val t = T.insert (trie, size, x)
        in
            A { size = size + 0w1, trie = t }
        end

    fun popEnd (A { size, trie }) =
        case T.find (trie, size - 0w1) of
            NONE => raise Empty
          | SOME x =>
            let val t = T.remove (trie, size - 0w1)
            in
                (A { size = size - 0w1, trie = t }, x)
            end

    fun sub (v as A { size, trie }, i) =
        if i < 0 orelse i >= length v
        then raise Subscript
        else T.lookup (trie, Word32.fromInt i)

    fun update (v as A { size, trie }, i, x) =
        if i < 0 orelse i >= length v
        then raise Subscript
        else let val t = T.insert (trie, Word32.fromInt i, x)
             in
                 A { size = size, trie = t }
             end

    fun foldr f acc (A { size, trie }) =
        T.foldr f acc trie

    fun fromList xx =
        List.foldl (fn (x, acc) => append (acc, x)) empty xx

    fun toList v =
        foldr (op::) [] v
end

structure PersistentArray = PersistentArrayImpl
