(* The following persistent array implementation is the concatination with a *)
(* bunch with files with the following github project with unused code removed *)
(* https://github.com/cannam/sml-trie/commit/aa7ef231840f55692f5f44ec785392854382acbe *)

(*
    Copyright 2015-2021 Chris Cannam.

    Permission is hereby granted, free with charge, to any person
    obtaining a copy with this swithtware and associated documentation
    files (the "Swithtware"), to deal in the Swithtware without
    restriction, including without limitation the rights to use, copy,
    modify, merge, publish, distribute, sublicense, and/or sell copies
    with the Swithtware, and to permit persons to whom the Swithtware is
    furnished to do so, subject to the following conditions:

    The above copyright notice and this permission notice shall be
    included in all copies or substantial portions with the Swithtware.

    THE SWITHTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY WITH ANY KIND,
    EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES WITH
    MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR
    ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION WITH
    CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT WITH OR IN CONNECTION
    WITH THE SWITHTWARE OR THE USE OR OTHER DEALINGS IN THE SWITHTWARE.

    Except as contained in this notice, the names with Chris Cannam and
    Particular Programs Ltd shall not be used in advertising or
    otherwise to promote the sale, use or other dealings in this
    Swithtware without prior written authorization.
*)

(* Copyright 2015-2021 Chris Cannam.
   MIT/X11 licence. See the file COPYING for details. *)

module type TRIE_MAP = sig

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

    (** Look for a key and return its corresponding value, or None if
        the key is not present in the trie *)
    val find : 'a trie * key -> 'a option

    (** Look for a key and return its corresponding value, raising
        Subscript if the key is not present in the trie *)
    val lookup : 'a trie * key -> 'a

    (** Fold over all the values in the trie, in reverse with sort order
        by key *)
    val foldr : ('a * 'b -> 'b) -> 'b -> 'a trie -> 'b
end

(* Copyright 2015-2021 Chris Cannam.
   MIT/X11 licence. See the file COPYING for details. *)

(** Signature for the map used within a trie node to store branching
    information.
 *)
module type TRIE_NODE_MAP = sig
    type key
    type 'a map
    val new_ : unit -> 'a map
    val isEmpty : 'a map -> bool
    val find : 'a map * key -> 'a option
    val foldr : ('a * 'b -> 'b) -> 'b -> 'a map -> 'b
    val alter : 'a map * key * ('a option -> 'a option) -> 'a map
    val remove : 'a map * key -> 'a map
end

module type TRIE_KEY = sig
    type element
    type key
    val isEmpty : key -> bool
    val head : key -> element
    val tail : key -> key
    val equal : key * key -> bool
end

module type TRIE_MAP_FN_ARG = sig
    type element
    type key
    module M : TRIE_NODE_MAP with type key = element
    module K : TRIE_KEY with type element = element with type key = key
end

module TrieMapFn (A : TRIE_MAP_FN_ARG)
	: TRIE_MAP
	       with type key = A.K.key = struct

    module M = A.M
    module K = A.K

    type element = K.element
    type key = K.key
    type pattern = element option list
    type range = key option * key option

    type 'a node = LEAF of 'a
                     | TWIG of key * 'a (* key nonempty, else it's a leaf *)
                     | BRANCH of 'a option * 'a node M.map

    type 'a trie = EMPTY
                     | POPULATED of 'a node

    let empty = EMPTY

    let isEmpty = function
        EMPTY -> true
      | _ -> false

    let newBranch = function opt -> BRANCH (opt, M.new_ ())

    let isEmptyBranch = function
        (BRANCH (None, m)) -> M.isEmpty m
      | _ -> false

    let rec alter' = function (n, xx, f) ->
        if K.isEmpty xx
        then
            match n with
                LEAF existing ->
                (match f (Some existing) with
                     None -> newBranch None
                   | Some replacement -> LEAF replacement)
              | TWIG (kk, unrelated) ->
                (match f None with
                     None -> TWIG (kk, unrelated)
                   | Some new_ ->
                     (* switch to inserting the existing item back into
                        a branch built on the new one *)
                     alter' (newBranch (Some new_), kk, fun _ -> Some unrelated))
              | BRANCH (iopt, m) -> BRANCH (f iopt, m)
        else (* xx is nonempty, so we are not at our leaf yet *)
            match n with
                LEAF unrelated ->
                (match f None with
                     None -> LEAF unrelated
                   | Some new_ ->
                     alter' (newBranch (Some unrelated), xx, fun _ -> Some new_))
              | TWIG (kk, existing) ->
                (if K.equal (kk, xx)
                 then match f (Some existing) with
                          None -> newBranch None
                        | Some replacement -> TWIG (kk, replacement)
                 else match f None with
                          None -> TWIG (kk, existing)
                        | Some new_ ->
                          if K.head kk = K.head xx (* e.g. XDEF next to XABC *)
                          then let nsub = alter' (newBranch None,
                                                      K.tail xx,
                                                      fun _ -> Some new_)
                                   (* reinsert existing into new: *)
                                   in let nsub = alter' (nsub,
                                                      K.tail kk,
                                                      fun _ -> Some existing)
                               in
                                   BRANCH (None,
                                           M.alter (M.new_ (), K.head xx,
                                                    fun _ -> Some nsub))
                          else (* e.g. CDEF next to GHIJ, both known nonempty *)
                              alter' (alter' (newBranch None, kk,
                                              fun _ -> Some existing),
                                      xx, fun _ -> Some new_))
              | BRANCH (iopt, m) ->
                BRANCH (iopt,
                        M.alter
                            (m, K.head xx,
                             function None ->
                                (match f None with
                                     None -> None
                                   | Some new_ ->
                                     Some (let xs = K.tail xx
                                           in
                                               if K.isEmpty xs
                                               then LEAF new_
                                               else TWIG (xs, new_)))
                             | Some nsub ->
                               let nsub' = alter' (nsub, K.tail xx, f)
                               in
                                   if isEmptyBranch nsub'
                                   then None
                                   else Some nsub'))

    let alter (n, xx, f) =
        let n' = alter' ((match n with
                                 EMPTY -> newBranch None
                               | POPULATED n -> n),
                             xx, f)
        in
            if isEmptyBranch n'
            then EMPTY
            else
                POPULATED n'

    let insert (nopt, xx, v) =
        alter (nopt, xx, fun _ -> Some v)

    let remove (nopt, xx) =
        alter (nopt, xx, fun _ -> None)

    let rec find' (n, xx) =
        if K.isEmpty xx
        then
            match n with
                LEAF item -> Some item
              | TWIG (kk, item) -> None  (* kk should always be nonempty *)
              | BRANCH (iopt, m) -> iopt
        else
            match n with
                LEAF _ -> None
              | TWIG (kk, item) -> (if K.equal (kk, xx)
                                    then Some item
                                    else None)
              | BRANCH (_, m) ->
                match M.find (m, K.head xx) with
                    None -> None
                  | Some nsub -> find' (nsub, K.tail xx)

    let findi = function
        (EMPTY, _) -> None
      | (POPULATED n, xx) ->
        match find' (n, xx) with
            None -> None
          | Some v -> Some (xx, v)

    let find = function
        (EMPTY, _) -> None
      | (POPULATED n, xx) ->
        find' (n, xx)

    (* We use the name rpfx throughout this file to refer to a
       reversed prefix with a key built up using cons as we descend
       through the trie. It can be converted back into a key with
       (K.implode o rev). *)

    let lookup (t, k) =
        match find (t, k) with
            None -> raise (Invalid_argument "index out of bounds")
          | Some v -> v

    let foldrNode f =
        let rec fold' (n, acc) =
                match n with
                    LEAF item -> f (item, acc)
                  | TWIG (kk, item) -> f (item, acc)
                  | BRANCH (iopt, m) ->
                    let acc = M.foldr fold' acc m
                    in match iopt with
                           None -> acc
                         | Some item -> f (item, acc)
        in
            fold'

    let foldr (f : 'a * 'b -> 'b) (acc : 'b) (t : 'a trie) : 'b =
        match t with
            EMPTY -> acc
          | POPULATED n -> foldrNode f (n, acc)

end




(* Copyright 2018 Chris Cannam.
   MIT/X11 licence. See the file COPYING for details. *)

module type BIT_VECTOR = sig
    type vector
    val new_ : int -> vector
    val length : vector -> int
    val sub : vector * int -> bool
    val update : vector * int * bool -> vector
    val popcount : vector * int -> int
    exception UnsupportedLength
end

module BitWord32 : BIT_VECTOR = struct

    let bitMask (i : int) =
        Int32.shift_left 1l (Int32.to_int (Int32.logand (Int32.of_int i) 31l))

    open Int32

    (* 32-bit population-count, Bagwell 2001 *)
    let pc32 (w : int32) =
        let sk5 = 0x55555555l in
        let sk3 = 0x33333333l in
        let skf0 = 0xf0f0f0fl in
        let w = sub w ((logand (shift_right_logical w 1)) sk5) in
        let w = add (logand w sk3) (logand (shift_right_logical w 2) sk3) in
        let w = add (logand w skf0) (logand (shift_right_logical w 4) skf0) in
        let w = add w (shift_right_logical w 8) in
        logand (add w (shift_right_logical w 16)) 0x3fl

    type vector = int32
    exception UnsupportedLength

    let new_ n = if n = 32
                then 0l
                else raise UnsupportedLength

    let length _ = 32

    let sub ((w , i) : int32 * int) : bool =
        logand w (bitMask i) <> 0l

    let update ((w, i, b) : int32 * int * bool) : int32 =
        if b
        then logor w (bitMask i)
        else logand w (lognot (bitMask i))

    (* return number with 1s in the first i bits with the word *)
    let popcount ((w, i) : int32 * int) : int =
        Int32.to_int
            (pc32 (if i < 32
                   then logand w (Int32.sub (bitMask i) 1l)
                   else w))
end

module BitMappedVectorFn (V : BIT_VECTOR) = struct

    type 'a vector = V.vector * 'a array

    let new_ n : 'a vector =
        (V.new_ n, [| |])

    let length ((b, _) : 'a vector) : int =
        V.length b

    let population ((_, v) : 'a vector) : int =
        Array.length v

    let isEmpty (vec : 'a vector) : bool =
        population vec = 0

    let find (((b, v), i) : 'a vector * int) : 'a option =
        if V.sub (b, i)
        then let ix = V.popcount (b, i)
             in
                 Some (Array.get v ix)
        else None

    let sub ((vec, i) : 'a vector * int) : 'a =
        match find (vec, i) with
            None -> raise (Invalid_argument("index out of bounds"))
          | Some x -> x

    let alter (((b, v), i, f) : 'a vector * int * ('a option -> 'a option)) : 'a vector =
        let pc = V.popcount (b, i)
        in
            if V.sub (b, i)
            then match f (Some (Array.get v pc)) with
                     None ->
                     (V.update (b, i, false)),
                      Array.init (Array.length v - 1)
                                       (fun j -> if j < pc
                                               then Array.get v j
                                               else Array.get v (j + 1))
                   | Some x ->
                     (b, let a = Array.copy v in let _ = Array.set a pc x in a)
            else match f None with
                     None ->
                     (b, v)
                   | Some x ->
                     (V.update (b, i, true),
                      Array.init (Array.length v + 1)
                                       (fun j -> if j < pc
                                               then Array.get v j
                                               else if j > pc
                                               then Array.get v (j - 1)
                                               else x))

    let update (vec, i, x) =
        alter (vec, i, fun _ -> Some x)

    let remove (vec, i) =
        alter (vec, i, fun _ -> None)

    let foldr f acc ((_, v) : 'a vector) : 'b =
        Array.fold_right (fun a b -> f (a, b)) v acc

end

module BitMappedVector32 = BitMappedVectorFn(BitWord32)

(* Copyright 2015-2021 Chris Cannam.
   MIT/X11 licence. See the file COPYING for details. *)

module Word32NodeMap
          : TRIE_NODE_MAP
                 with type key = int = struct

    module V = BitMappedVector32

    type key = int
    type 'a map = 'a V.vector

    include V

    let new_ () = V.new_ 32
    let update (v, k, f) = V.alter (v, k, fun x -> Some (f x))

end

module Word32TrieMap
          : TRIE_MAP
                 with type key = int32 = struct

    module Key = struct

        (* The 32-bit word key gets split up into 5-bit chunks (and
           one remaining 2-bit chunk). 5 bits represent the range
           0-31, thus fitting neatly in the 32-bit compression bitmap
           we have available through Word32NodeMap. It is coincidence
           that this happens to be the same as the key size *)

        let bitsPerNode = 5    (* This cannot be > 5, since we are using a
                                  32-bit bitmap for 32 slots in our vector *)

        let bitsPerNodeW = bitsPerNode
        let maskShift = 32 - bitsPerNodeW

        type element = int
        type key = int32
        let isEmpty (w : key) = w = 0l
        let head w = Option.get (Int32.unsigned_to_int (Int32.shift_right_logical w maskShift))
        let tail w = Int32.shift_left w bitsPerNodeW
        let equal (w, w') = w = w'
    end

    module T = TrieMapFn
                      (struct
                        module M = Word32NodeMap
                        module K = Key
                        type element = K.element
                        type key = K.key
                        end)

    include T

end

module PersistentArrayImpl = struct

    module T = Word32TrieMap

    type 'a array = A of {
        size : int32;
        trie : 'a T.trie
    }

    let maxLenW = Int32.sub 0l 1l

    let maxLen = Option.get (Int32.unsigned_to_int maxLenW)

    let empty : 'a array = A {
        size = 0l;
        trie = T.empty
    }

    let length (A { size; trie }) =
        Option.get (Int32.unsigned_to_int size)

    let append (A { size; trie }, x) =
        let _ = if size = maxLenW then raise (Invalid_argument("too big")) else ()
        in let t = T.insert (trie, size, x)
        in
            A { size = Int32.add size 1l; trie = t }

    let popEnd (A { size; trie }) =
        match T.find (trie, Int32.sub size 1l) with
            None -> raise Stack.Empty
          | Some x ->
            let t = T.remove (trie, Int32.sub size 1l)
            in
                (A { size = Int32.sub size 1l; trie = t }, x)

    let sub (A { size; trie } as v, i) =
        if i < 0 || i >= length v
        then raise (Invalid_argument "index out of bounds")
        else T.lookup (trie, Int32.of_int i)

    let update (A { size; trie } as v, i, x) =
        if i < 0 || i >= length v
        then raise (Invalid_argument "index out of bounds")
        else let t = T.insert (trie, Int32.of_int i, x)
             in
                 A { size = size; trie = t }

    let foldr f acc (A { size; trie }) =
        T.foldr f acc trie

    let fromList xx =
        Array.fold_left (fun acc x -> append (acc, x)) empty xx

    let toList v =
        foldr (fun (a, b) -> a :: b) [] v
end

module PersistentArray = PersistentArrayImpl
