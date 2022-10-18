(* The following persistent array implementation is the concatination of a *)
(* burch of files of the following github project: *)
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

    (** Alter a key-value pair in the trie, returning a new trie. The
        function argument should map from the previous value
        associated with the key, or NONE if it was absent before, to
        the new value, or NONE if it is to be removed. (This is called
        alter rather than modify to avoid confusion with the array
        modify functions, which do something rather different) *)
    val alter : 'a trie * key * ('a option -> 'a option) -> 'a trie

    (** Insert a key-value pair, returning a new trie. If the key is
        already present, its value will be updated in the new trie *)
    val insert : 'a trie * key * 'a -> 'a trie

    (** Return the trie with the given key removed. If the key is
        not present, the returned trie will be unchanged *)
    val remove : 'a trie * key -> 'a trie

    (** Test whether the trie contains the given key *)
    val contains : 'a trie * key -> bool

    (** Look for a key and return its corresponding value, or NONE if
        the key is not present in the trie *)
    val find : 'a trie * key -> 'a option

    (** Look for a key and return its corresponding value, raising
        Subscript if the key is not present in the trie *)
    val lookup : 'a trie * key -> 'a

    (** Look for the closest key to the given one and return it with
        its corresponding value. If order is EQUAL, then a result is
        returned only if the given key is actually in the trie (like
        find); if order is LESS or GREATER, the given key is still
        returned if it exists, but otherwise the next key comparing
        respectively less or greater than it is returned, if there is
        one *)
    val locate : 'a trie * key * order -> (key * 'a) option

    (** Return the longest prefix of the given key that is present as
        a key in the trie. The given key does not need to be present
        as a key in the trie. If it is present, it will be its own
        longest prefix, and so it will be returned. If there is no
        prefix of the given key in the trie, return NONE *)
    val prefixOf : 'a trie * key -> key option

    (** Examine the values in the trie, in sort order by key, and
        return the first one for which the given function returns
        true. This is similar to Vector.find in that it must iterate
        through the trie rather than performing a direct lookup *)
    val search : ('a -> bool) -> 'a trie -> 'a option

    (** Examine the key/value pairs in the trie, in sort order by key,
        and return the first one for which the given function returns
        true. This is similar to Vector.findi in that it must iterate
        through the trie rather than performing a direct lookup *)
    val searchi : (key * 'a -> bool) -> 'a trie -> (key * 'a) option

    (** Map all the values in the trie to new values using the given
        map function, supplied with key and value for each. *)
    val mapi : (key * 'a -> 'b) -> 'a trie -> 'b trie

    (** Map all the values in the trie to new values using the given
        map function, supplied with value only. *)
    val map : ('a -> 'b) -> 'a trie -> 'b trie

    (** Fold over all the key-value pairs in the trie, in sort order
        by key *)
    val foldli : (key * 'a * 'b -> 'b) -> 'b -> 'a trie -> 'b

    (** Fold over all the values in the trie, in sort order by key *)
    val foldl : ('a * 'b -> 'b) -> 'b -> 'a trie -> 'b

    (** Fold over all the key-value pairs in the trie, in reverse of
        sort order by key *)
    val foldri : (key * 'a * 'b -> 'b) -> 'b -> 'a trie -> 'b

    (** Fold over all the values in the trie, in reverse of sort order
        by key *)
    val foldr : ('a * 'b -> 'b) -> 'b -> 'a trie -> 'b

    (** Return a list of all key-value pairs in the trie, in sort order
        by key *)
    val enumerate : 'a trie -> (key * 'a) list

    (** Fold over all the key-value pairs in the trie that have the
        given prefix, in sort order by key. The prefix itself does not
        need to be present as a key in the trie *)
    val foldliPrefix : (key * 'a * 'b -> 'b) -> 'b -> ('a trie * key) -> 'b

    (** Fold over all the key-value pairs in the trie that have the
        given prefix, in reverse of sort order by key. The prefix
        itself does not need to be present as a key in the trie *)
    val foldriPrefix : (key * 'a * 'b -> 'b) -> 'b -> ('a trie * key) -> 'b

    (** Return a trie containing all key-value pairs in the trie that
        have the given key as a prefix, sharing the structure of the
        given trie as far as possible. The prefix itself does not need
        to be present as a key in the trie *)
    val extractPrefix : 'a trie * key -> 'a trie

    (** Return a list of all key-value pairs in the trie that have the
        given key as a prefix, in sort order by key. The prefix itself
        does not need to be present as a key in the trie *)
    val enumeratePrefix : 'a trie * key -> (key * 'a) list

    (** Inclusive range of keys (first, last). If either is NONE, then
        the range is unbounded on that side *)
    type range = key option * key option

    (** Fold over all the values in the trie that are found within the
        given key range, in sort order by key *)
    val foldlRange : ('a * 'b -> 'b) -> 'b -> ('a trie * range) -> 'b

    (** Fold over all the key-value pairs in the trie that are found
        within the given key range, in sort order by key *)
    val foldliRange : (key * 'a * 'b -> 'b) -> 'b -> ('a trie * range) -> 'b

    (** Fold over all the values in the trie that are found within the
        given key range, in reverse of sort order by key *)
    val foldrRange : ('a * 'b -> 'b) -> 'b -> ('a trie * range) -> 'b

    (** Fold over all the key-value pairs in the trie that are found
        within the given key range, in reverse of sort order by key *)
    val foldriRange : (key * 'a * 'b -> 'b) -> 'b -> ('a trie * range) -> 'b

    (** Return the keys at either end of the given range. That is,
        return keys k1 and k2, present in the trie, for which the
        range (SOME k1, SOME k2) is equivalent to the given range
        within the given trie. If the given range is empty within the
        given trie, return NONE. This is equivalent to checking the
        first keys of foldli/foldriRange, but typically faster. *)
    val resolveRange : 'a trie * range -> (key * key) option

    (** Return a trie containing all key-value pairs in the trie that
        are found within the given key range, sharing the structure of
        the given trie as far as possible *)
    val extractRange : 'a trie * range -> 'a trie

    (** Return a list of all key-value pairs in the trie that are
        found within the given key range, in sort order by key *)
    val enumerateRange : 'a trie * range -> (key * 'a) list

end

(* Copyright 2015-2021 Chris Cannam.
   MIT/X11 licence. See the file COPYING for details. *)

signature PATTERN_MATCH_TRIE_MAP = sig

    (* This is a trie that can do pattern matches as well as prefix
       matches. Say you have a trie containing some (conceptual)
       list/string entries matching ABB, ABC, and BBC. With the plain
       trie you can match e.g. prefix AB to return ABB and ABC. With a
       pattern-match trie you can alternatively provide a query list
       like [NONE, SOME B, NONE] to return all entries having three
       elements with B in the middle, here all three of the listed
       entries.

       This differs from the plain trie not only because of the
       additional pattern match function, but also because the type of
       the individual node elements is exposed, whereas TRIE uses an
       atomic entry type. *)

    include TRIE_MAP

    type element
    type pattern = element option list

    (* Fold over all the key-value pairs in the trie that match the
       given pattern, in sort order. Will only return entries with
       exactly the same number of elements as values in the pattern *)
    val foldliPattern : (key * 'a * 'b -> 'b) -> 'b -> ('a trie * pattern) -> 'b

    (* Fold over all the key-value pairs in the trie that match the
       given pattern, in reverse of sort order. Will only return
       entries with exactly the same number of elements as values in
       the pattern *)
    val foldriPattern : (key * 'a * 'b -> 'b) -> 'b -> ('a trie * pattern) -> 'b

    (* Return all the key-value pairs in the trie that match the given
       pattern, in sort order. Will only return entries with exactly
       the same number of elements as values in the pattern *)
    val enumeratePattern : ('a trie * pattern) -> (key * 'a) list

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
    val map : ('a -> 'b) -> 'a map -> 'b map
    val mapi : (key * 'a -> 'b) -> 'a map -> 'b map
    val foldl : ('a * 'b -> 'b) -> 'b -> 'a map -> 'b
    val foldli : (key * 'a * 'b -> 'b) -> 'b -> 'a map -> 'b
    val foldr : ('a * 'b -> 'b) -> 'b -> 'a map -> 'b
    val foldri : (key * 'a * 'b -> 'b) -> 'b -> 'a map -> 'b
    val alter : 'a map * key * ('a option -> 'a option) -> 'a map
    val remove : 'a map * key -> 'a map
    val keyCompare : key * key -> order
end

signature TRIE_KEY = sig
    eqtype element
    type key
    val isEmpty : key -> bool
    val head : key -> element
    val tail : key -> key
    val explode : key -> element list
    val implode : element list -> key
    val equal : key * key -> bool
end

signature TRIE_MAP_FN_ARG = sig
    eqtype element
    type key
    structure M : TRIE_NODE_MAP where type key = element
    structure K : TRIE_KEY where type element = element where type key = key
end

functor TrieMapFn (A : TRIE_MAP_FN_ARG)
	:> PATTERN_MATCH_TRIE_MAP
	       where type element = A.K.element where type key = A.K.key = struct

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

    fun isCanonical n =
        case n of
            LEAF _ => true
          | TWIG (k, _) =>
            if K.isEmpty k
            then (print "Not canonical: twig with empty key\n"; false)
            else true
          | BRANCH (NONE, m) =>
            if M.isEmpty m
            then
                (print "Not canonical: empty branch\n"; false)
            else true
          | BRANCH (_, m) =>
            if M.foldl (fn (mi, acc) => acc orelse isEmptyBranch mi)
                       false m
            then
                (print "Not canonical: branch with empty sub-branch\n"; false)
            else if M.foldl (fn (mi, acc) => acc orelse not (isCanonical mi))
                            false m
            then
                (print "Not canonical: branch with non-canonical sub-branch\n"; false)
            else true

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
(*                let val _ = if not (isCanonical n')
                            then print "NOT CANONICAL\n"
                            else ()
                in *)
                    POPULATED n'
(*                end *)
        end

    fun insert (nopt, xx, v) =
        alter (nopt, xx, fn _ => SOME v)

    fun remove (nopt, xx) =
        alter (nopt, xx, fn _ => NONE)

    fun isPrefixOf ([], yy) = true
      | isPrefixOf (xx, []) = false
      | isPrefixOf (x::xs, y::ys) = x = y andalso isPrefixOf (xs, ys)

    fun compareKeys (kk, kk') =
        case (kk, kk') of
            ([], []) => EQUAL
          | ([],  _) => LESS
          | (_,  []) => GREATER
          | (k::ks, k'::ks') => case M.keyCompare (k, k') of
                                    EQUAL => compareKeys (ks, ks')
                                  | other => other

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

    fun locate' (folder, order) =
        let fun boundaryItem (n, rpfx) =
                case n of
                    LEAF item => SOME (rpfx, item)
                  | TWIG (kk, item) => SOME (rev (K.explode kk) @ rpfx, item)
                  | BRANCH (SOME item, m) =>
                    (* In a canonical structure (which we are supposed
                       to be) a branch always has at least one
                       subnode, so we only have to consider the branch
                       item if we are looking for the first item in
                       the branch (in which case it's it) - otherwise
                       we go straight to the subnodes *)
                    if order = LESS
                    then boundaryItem (BRANCH (NONE, m), rpfx)
                    else SOME (rpfx, item)
                  | BRANCH (NONE, m) =>
                    folder (fn (_, _, SOME result) => SOME result
                             | (k, n', NONE) => boundaryItem (n', k::rpfx))
                           NONE m

            fun locate'' (n, xx, rpfx) =
                if K.isEmpty xx
                then if order = GREATER
                     then boundaryItem (n, rpfx)
                     else case n of
                              LEAF item => SOME (rpfx, item)
                            | BRANCH (SOME item, _) => SOME (rpfx, item)
                            | _ => NONE
                else
                    case n of
                        LEAF item =>
                        if order = LESS
                        then SOME (rpfx, item)
                        else NONE
                      | TWIG (kk, item) =>
                        if compareKeys (K.explode xx, K.explode kk) <> order
                        then boundaryItem (n, rpfx)
                        else NONE
                      | BRANCH (iopt, m) =>
                        let val (x, xs) = (K.head xx, K.tail xx)
                        in case folder (fn (_, _, SOME result) => SOME result
                                         | (k, n', NONE) =>
                                           case M.keyCompare (k, x) of
                                               EQUAL => locate'' (n', xs, k::rpfx)
                                             | other =>
                                               if other = order
                                               then boundaryItem (n', k::rpfx)
                                               else NONE)
                                       NONE
                                       m
                            of SOME result => SOME result
                             | NONE =>
                               if order = GREATER
                               then NONE
                               else Option.map (fn item => (rpfx, item)) iopt
                        end
        in
            locate''
        end

    fun locate (EMPTY, xx, ord) = NONE
      | locate (POPULATED n, xx, ord) =
        let val conv = Option.map (fn (kk, item) => (K.implode (rev kk), item))
        in
            case ord of
                LESS => conv (locate' (M.foldri, LESS) (n, xx, []))
              | EQUAL => findi (POPULATED n, xx)
              | GREATER => conv (locate' (M.foldli, GREATER) (n, xx, []))
        end

    fun lookup (t, k) =
        case find (t, k) of
            NONE => raise Subscript
          | SOME v => v

    fun contains (t, k) =
        case find (t, k) of
            SOME _ => true
          | NONE => false

    fun searchNode f =
        let fun search' n =
                case n of
                    LEAF item => if f item
                                 then SOME item
                                 else NONE
                  | TWIG (kk, item) => if f item
                                       then SOME item
                                       else NONE
                  | BRANCH (iopt, m) =>
                    if Option.isSome iopt andalso f (Option.valOf iopt)
                    then iopt
                    else M.foldl (fn (n', SOME r) => SOME r
                                   | (n', NONE) => search' n')
                                 NONE
                                 m
        in
            search'
        end

    fun search (f : 'a -> bool) (t : 'a trie) : 'a option =
        case t of
            EMPTY => NONE
          | POPULATED n => searchNode f n

    fun searchiNode f =
        let fun searchi' (rpfx, n) =
                case n of
                    LEAF item =>
                    let val k = K.implode (rev rpfx)
                    in
                        if f (k, item)
                        then SOME (k, item)
                        else NONE
                    end
                  | TWIG (kk, item) =>
                    let val k = K.implode (rev rpfx @ K.explode kk)
                    in
                        if f (k, item)
                        then SOME (k, item)
                        else NONE
                    end
                  | BRANCH (iopt, m) =>
                    let val k = K.implode (rev rpfx)
                    in
                        if Option.isSome iopt andalso f (k, Option.valOf iopt)
                        then SOME (k, Option.valOf iopt)
                        else M.foldli (fn (x, n', SOME r) => SOME r
                                        | (x, n', NONE) =>
                                          searchi' (x::rpfx, n'))
                                      NONE
                                      m
                    end
        in
            searchi'
        end

    fun searchi (f : key * 'a -> bool) (t : 'a trie) : (key * 'a) option =
        case t of
            EMPTY => NONE
          | POPULATED n => searchiNode f ([], n)

    fun mapiNode f =
        let fun f' (rpfx, item) = f (K.implode (rev rpfx), item)
            fun mapi' (rpfx, n) =
                case n of
                    LEAF item =>
                    LEAF (f' (rpfx, item))
                  | TWIG (kk, item) =>
                    TWIG (kk, f' (rpfx, item))
                  | BRANCH (iopt, m) =>
                    BRANCH (Option.map (fn item => f' (rpfx, item)) iopt,
                            M.mapi (fn (x, n) => mapi' (x::rpfx, n)) m)
        in
            mapi'
        end

    fun mapi (f : key * 'a -> 'b) (t : 'a trie) : 'b trie =
        case t of
            EMPTY => EMPTY
          | POPULATED n =>
            POPULATED (mapiNode f ([], n))

    fun mapNode f n =
        case n of
            LEAF item => LEAF (f item)
          | TWIG (kk, item) => TWIG (kk, f item)
          | BRANCH (iopt, m) => BRANCH (Option.map f iopt, M.map (mapNode f) m)

    fun map (f : 'a -> 'b) (t : 'a trie) : 'b trie =
        case t of
            EMPTY => EMPTY
          | POPULATED n => POPULATED (mapNode f n)

    fun foldlNode f =
        let fun fold' (n, acc) =
                case n of
                    LEAF item => f (item, acc)
                  | TWIG (kk, item) => f (item, acc)
                  | BRANCH (iopt, m) =>
                    let val acc = case iopt of
                                      NONE => acc
                                    | SOME item => f (item, acc)
                    in M.foldl fold' acc m
                    end
        in
            fold'
        end

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

    fun foldl (f : 'a * 'b -> 'b) (acc : 'b) (t : 'a trie) : 'b =
        case t of
            EMPTY => acc
          | POPULATED n => foldlNode f (n, acc)

    fun foldr (f : 'a * 'b -> 'b) (acc : 'b) (t : 'a trie) : 'b =
        case t of
            EMPTY => acc
          | POPULATED n => foldrNode f (n, acc)

    fun foldliNode f =
        let fun f' (rpfx, item, acc) = f (K.implode (rev rpfx), item, acc)
            fun foldli' (rpfx, n, acc) =
                case n of
                    LEAF item =>
                    f' (rpfx, item, acc)
                  | TWIG (kk, item) =>
                    f' ((rev (K.explode kk)) @ rpfx, item, acc)
                  | BRANCH (iopt, m) =>
                    M.foldli (fn (x, n, acc) => foldli' (x::rpfx, n, acc))
                             (case iopt of
                                  NONE => acc
                                | SOME item => f' (rpfx, item, acc))
                             m
        in
            foldli'
        end

    fun foldriNode f =
        let fun f' (rpfx, item, acc) = f (K.implode (rev rpfx), item, acc)
            fun foldri' (rpfx, n, acc) =
                case n of
                    LEAF item =>
                    f' (rpfx, item, acc)
                  | TWIG (kk, item) =>
                    f' ((rev (K.explode kk)) @ rpfx, item, acc)
                  | BRANCH (iopt, m) =>
                    let val acc = M.foldri (fn (x, n, acc) =>
                                               foldri' (x::rpfx, n, acc)) acc m
                    in
                        case iopt of
                            NONE => acc
                          | SOME item => f' (rpfx, item, acc)
                    end
        in
            foldri'
        end

    fun foldli f acc t =
        case t of
            EMPTY => acc
          | POPULATED n => foldliNode f ([], n, acc)

    fun foldri f acc t =
        case t of
            EMPTY => acc
          | POPULATED n => foldriNode f ([], n, acc)

    fun enumerate trie =
        foldri (fn (k, v, acc) => (k, v) :: acc) [] trie

    fun foldiPrefixNode nodeFolder f =
        let fun foldi' (rpfx, n, xx, acc) =
                if K.isEmpty xx
                then nodeFolder f (rpfx, n, acc)
                else
                    case n of
                        LEAF item => acc
                      | TWIG (kk, item) =>
                        (if isPrefixOf (K.explode xx, K.explode kk)
                         then nodeFolder f (rpfx, n, acc)
                         else acc)
                      | BRANCH (_, m) =>
                        case M.find (m, K.head xx) of
                            NONE => acc
                          | SOME nsub =>
                            foldi' ((K.head xx) :: rpfx, nsub, (K.tail xx), acc)
        in
            foldi'
        end

    fun foldliPrefix f acc (trie, e) =
        case trie of
            EMPTY => acc
          | POPULATED n => foldiPrefixNode foldliNode f ([], n, e, acc)

    fun foldriPrefix f acc (trie, e) =
        case trie of
            EMPTY => acc
          | POPULATED n => foldiPrefixNode foldriNode f ([], n, e, acc)

    fun enumeratePrefix (trie, e) =
        foldriPrefix (fn (k, v, acc) => (k, v) :: acc) [] (trie, e)

    fun extractPrefixNode (n, xx) =
        if K.isEmpty xx
        then POPULATED n
        else
            case n of
                LEAF item => EMPTY
              | TWIG (kk, item) =>
                (if isPrefixOf (K.explode xx, K.explode kk)
                 then POPULATED n
                 else EMPTY)
              | BRANCH (_, m) =>
                case M.find (m, K.head xx) of
                    NONE => EMPTY
                  | SOME nsub =>
                    case extractPrefixNode (nsub, K.tail xx) of
                        EMPTY => EMPTY
                      | POPULATED nsub' =>
                        POPULATED (BRANCH (NONE, M.alter (M.new (), K.head xx,
                                                          fn _ => SOME nsub')))

    fun extractPrefix (trie, e) =
        case trie of
            EMPTY => EMPTY
          | POPULATED n => extractPrefixNode (n, e)

    local
        (* The functions to which these are local (foldiRangeNode,
           foldRangeNode, extractRangeNode) still have quite a lot of
           duplication between them, but it's not immediately obvious
           to me how to factor that out without jeopardising
           performance.

           Note that first function (foldiRangeNode) has some comments
           that are relevant to all three. The subsequent two are
           essentially modified versions of it.
         *)

        fun acceptTwig (kk, lc, rc) =
            (null lc orelse compareKeys (kk, lc) <> LESS)
            andalso
            (null rc orelse compareKeys (kk, rc) <> GREATER)

        fun subConstraint (x, []) = NONE
          | subConstraint (x, c::cs) = if c = x
                                       then SOME (K.implode cs)
                                       else NONE

        fun acceptMapElement (x, lc, rc) =
            (null lc orelse M.keyCompare (x, hd lc) <> LESS)
            andalso
            (null rc orelse M.keyCompare (x, hd rc) <> GREATER)

    in
    fun foldiRangeNode right f (rpfx, n, leftConstraintK, rightConstraintK, acc) =
        let fun f' (pfx, item, acc) =
                f (K.implode pfx, item, acc)

            (* When foldiRangeNode is entered, leftConstraint and
               rightConstraint may be NONE (no constraint), SOME []
               (constraint at start of this node), or SOME other
               (constraint on sub-node). For leftConstraint there is
               no distinction between NONE and SOME [], so we can just
               pass the optional list or [] if there was none. For
               rightConstraint, there is a distinction, but it is that
               we don't want to call the node traversal function at
               all if the constraint is SOME []. So we can similarly
               just pass the optional list, passing [] if there was
               none but not calling at all if there was one and it was
               empty. So we don't need an option in these functions -
               an empty list represents "no constraint" rather than a
               constraint at the start of the node.

               We use the names leftConstraint/rightConstraint to
               refer to the option types and lc/rc to refer to these
               unwrapped versions. *)

            fun leaf (item, [], _) = f' (rev rpfx, item, acc)
              | leaf _ = acc

            fun twig ((kk, item), lc, rc) =
                let val kk' = K.explode kk
                in
                    if acceptTwig (kk', lc, rc)
                    then f' ((rev rpfx) @ kk', item, acc)
                    else acc
                end

            fun branchl ((iopt, m), [], []) =
                foldliNode f (rpfx, n, acc)
              | branchl ((iopt, m), lc, rc) =
                M.foldli
                    (fn (x, nsub, acc) =>
                        if not (acceptMapElement (x, lc, rc)) then acc
                        else foldiRangeNode false
                                            f (x :: rpfx, nsub,
                                               subConstraint (x, lc),
                                               subConstraint (x, rc),
                                               acc))
                    (case iopt of
                         NONE => acc
                       | SOME item => case lc of
                                          [] => f' (rev rpfx, item, acc)
                                        | _ => acc)
                    m

            fun branchr ((iopt, m), [], []) =
                foldriNode f (rpfx, n, acc)
              | branchr ((iopt, m), lc, rc) =
                let val acc =
                        M.foldri
                            (fn (x, nsub, acc) =>
                                if not (acceptMapElement (x, lc, rc)) then acc
                                else foldiRangeNode true
                                                    f (x :: rpfx, nsub,
                                                       subConstraint (x, lc),
                                                       subConstraint (x, rc),
                                                       acc))
                            acc m
                in
                    case iopt of
                        NONE => acc
                      | SOME item => case lc of
                                         [] => f' (rev rpfx, item, acc)
                                       | _ => acc
                end

            val branch = if right then branchr else branchl

            val leftConstraint = Option.map K.explode leftConstraintK
            val rightConstraint = Option.map K.explode rightConstraintK

            val lc = Option.getOpt (leftConstraint, [])
            val rc = Option.getOpt (rightConstraint, [])
        in
            case rightConstraint of
                SOME [] =>
                (* if we have a leaf or branch-with-item, we should
                   accept the item - since our ranges are inclusive -
                   but we shouldn't recurse or follow a twig *)
                (if null lc
                 then case n of
                          LEAF item => leaf (item, lc, NONE)
                        | TWIG _ => acc
                        | BRANCH (NONE, _) => acc
                        | BRANCH (SOME item, _) => f' (rev rpfx, item, acc)
                 else acc)
              | _ =>
                (case n of
                     LEAF item => leaf (item, lc, rc)
                   | TWIG (kk, item) => twig ((kk, item), lc, rc)
                   | BRANCH (iopt, m) => branch ((iopt, m), lc, rc))
        end

    fun foldRangeNode right f (n, leftConstraintK, rightConstraintK, acc) =
        let (* this is identical to foldiRangeNode but with prefix
               args removed everywhere *)

            fun leaf (item, [], _) = f (item, acc)
              | leaf _ = acc

            fun twig ((kk, item), lc, rc) =
                let val kk' = K.explode kk
                in
                    if acceptTwig (kk', lc, rc)
                    then f (item, acc)
                    else acc
                end

            fun branchl ((iopt, m), [], []) =
                foldlNode f (n, acc)
              | branchl ((iopt, m), lc, rc) =
                M.foldli
                    (fn (x, nsub, acc) =>
                        if not (acceptMapElement (x, lc, rc)) then acc
                        else foldRangeNode false
                                           f (nsub,
                                              subConstraint (x, lc),
                                              subConstraint (x, rc),
                                              acc))
                    (case iopt of
                         NONE => acc
                       | SOME item => case lc of
                                          [] => f (item, acc)
                                        | _ => acc)
                    m

            fun branchr ((iopt, m), [], []) =
                foldrNode f (n, acc)
              | branchr ((iopt, m), lc, rc) =
                let val acc =
                        M.foldri
                            (fn (x, nsub, acc) =>
                                if not (acceptMapElement (x, lc, rc)) then acc
                                else foldRangeNode true
                                                   f (nsub,
                                                      subConstraint (x, lc),
                                                      subConstraint (x, rc),
                                                      acc))
                            acc m
                in
                    case iopt of
                        NONE => acc
                      | SOME item => case lc of
                                         [] => f (item, acc)
                                       | _ => acc
                end

            val branch = if right then branchr else branchl

            val leftConstraint = Option.map K.explode leftConstraintK
            val rightConstraint = Option.map K.explode rightConstraintK

            val lc = Option.getOpt (leftConstraint, [])
            val rc = Option.getOpt (rightConstraint, [])
        in
            (* see notes in foldiRangeNode *)
            case rightConstraint of
                SOME [] =>
                (if null lc
                 then case n of
                          LEAF item => leaf (item, lc, NONE)
                        | TWIG _ => acc
                        | BRANCH (NONE, _) => acc
                        | BRANCH (SOME item, _) => f (item, acc)
                 else acc)
              | _ =>
                (case n of
                     LEAF item => leaf (item, lc, rc)
                   | TWIG (kk, item) => twig ((kk, item), lc, rc)
                   | BRANCH (iopt, m) => branch ((iopt, m), lc, rc))
        end

    fun resolveRangeNode right (rpfx, n, leftConstraintK, rightConstraintK) =
        let fun leaf (item, [], _) = SOME (K.implode (rev rpfx))
              | leaf _ = NONE

            fun twig ((kk, item), lc, rc) =
                let val kk' = K.explode kk
                in
                    if acceptTwig (kk', lc, rc)
                    then SOME (K.implode ((rev rpfx) @ kk'))
                    else NONE
                end

            fun branchl ((SOME item, m), [], rc) =
                SOME (K.implode (rev rpfx))
              | branchl ((iopt, m), [], []) =
                foldliNode (fn (k, _, NONE) => SOME k
                             | (_, _, acc) => acc)
                           (rpfx, n, NONE)
              | branchl ((iopt, m), lc, rc) =
                M.foldli
                    (fn (x, nsub, SOME k) => SOME k
                      | (x, nsub, NONE) =>
                        if not (acceptMapElement (x, lc, rc)) then NONE
                        else resolveRangeNode false
                                              (x :: rpfx, nsub,
                                               subConstraint (x, lc),
                                               subConstraint (x, rc)))
                    NONE m

            fun branchr ((iopt, m), [], []) =
                foldriNode (fn (k, _, NONE) => SOME k
                             | (_, _, acc) => acc)
                           (rpfx, n, NONE)
              | branchr ((iopt, m), lc, rc) =
                let val acc =
                        M.foldri
                            (fn (x, nsub, SOME k) => SOME k
                              | (x, nsub, NONE) =>
                                if not (acceptMapElement (x, lc, rc)) then NONE
                                else resolveRangeNode true
                                                      (x :: rpfx, nsub,
                                                       subConstraint (x, lc),
                                                       subConstraint (x, rc)))
                            NONE m
                in
                    case acc of
                        SOME k => SOME k
                      | NONE =>
                        case iopt of
                            NONE => NONE
                          | SOME item => case lc of
                                             [] => SOME (K.implode (rev rpfx))
                                           | _ => NONE
                end

            val branch = if right then branchr else branchl

            val leftConstraint = Option.map K.explode leftConstraintK
            val rightConstraint = Option.map K.explode rightConstraintK

            val lc = Option.getOpt (leftConstraint, [])
            val rc = Option.getOpt (rightConstraint, [])
        in
            case rightConstraint of
                SOME [] =>
                (if null lc
                 then case n of
                          LEAF item => leaf (item, lc, NONE)
                        | TWIG _ => NONE
                        | BRANCH (NONE, _) => NONE
                        | BRANCH (SOME item, _) => SOME (K.implode (rev rpfx))
                 else NONE)
              | _ =>
                (case n of
                     LEAF item => leaf (item, lc, rc)
                   | TWIG (kk, item) => twig ((kk, item), lc, rc)
                   | BRANCH (iopt, m) => branch ((iopt, m), lc, rc))
        end

    fun extractRangeNode (n, leftConstraintK, rightConstraintK) =
        let (* quite some duplication with foldiRangeNode here *)
            fun leaf (item, [], _) = POPULATED (LEAF item)
              | leaf _ = EMPTY

            fun twig (tw as (kk, item), lc, rc) =
                if acceptTwig (K.explode kk, lc, rc)
                then POPULATED (TWIG tw)
                else EMPTY

            fun branch ((iopt, m), [], []) = POPULATED (BRANCH (iopt, m))
              | branch ((iopt, m), lc, rc) =
                let val m' =
                        M.foldli
                            (fn (x, nsub, acc) =>
                                if not (acceptMapElement (x, lc, rc))
                                then acc
                                else case extractRangeNode
                                              (nsub,
                                               subConstraint (x, lc),
                                               subConstraint (x, rc)) of
                                         EMPTY => acc
                                       | POPULATED nsub' =>
                                         M.alter (acc, x, fn _ => SOME nsub'))
                            (M.new ())
                            m
                in
                    if M.isEmpty m'
                    then case iopt of
                             NONE => EMPTY
                           | SOME i => case lc of
                                           [] => POPULATED (LEAF i)
                                         | _ => EMPTY
                    else POPULATED
                             (BRANCH
                                  (case (iopt, lc) of
                                       (SOME i, []) => iopt
                                     | _ => NONE,
                                   m'))
                end

            val leftConstraint = Option.map K.explode leftConstraintK
            val rightConstraint = Option.map K.explode rightConstraintK

            val lc = Option.getOpt (leftConstraint, [])
            val rc = Option.getOpt (rightConstraint, [])
        in
            (* see notes in foldiRangeNode *)
            case rightConstraint of
                SOME [] =>
                (if null lc
                 then case n of
                          LEAF item => POPULATED n
                        | TWIG _ => EMPTY
                        | BRANCH (NONE, _) => EMPTY
                        | BRANCH (SOME item, _) => POPULATED (LEAF item)
                 else EMPTY)
             | _ =>
               (case n of
                    LEAF item => leaf (item, lc, rc)
                  | TWIG (kk, item) => twig ((kk, item), lc, rc)
                  | BRANCH (iopt, m) => branch ((iopt, m), lc, rc))
        end
    end (* end local *)

    fun foldliRange f acc (t, (leftConstraint, rightConstraint)) =
        case t of
            EMPTY => acc
          | POPULATED n =>
            foldiRangeNode false
                           f ([], n, leftConstraint, rightConstraint, acc)

    fun foldriRange f acc (t, (leftConstraint, rightConstraint)) =
        case t of
            EMPTY => acc
          | POPULATED n =>
            foldiRangeNode true
                           f ([], n, leftConstraint, rightConstraint, acc)

    fun foldlRange f acc (t, (leftConstraint, rightConstraint)) =
        case t of
            EMPTY => acc
          | POPULATED n =>
            foldRangeNode false f (n, leftConstraint, rightConstraint, acc)

    fun foldrRange f acc (t, (leftConstraint, rightConstraint)) =
        case t of
            EMPTY => acc
          | POPULATED n =>
            foldRangeNode true f (n, leftConstraint, rightConstraint, acc)

    fun resolveRange (trie, (leftConstraint, rightConstraint)) =
        case trie of
            EMPTY => NONE
          | POPULATED n =>
            case (resolveRangeNode false
                                   ([], n, leftConstraint, rightConstraint),
                  resolveRangeNode true
                                   ([], n, leftConstraint, rightConstraint)) of
                (NONE, NONE) => NONE
              | (SOME left, SOME right) => SOME (left, right)
              | _ =>
                raise Fail "internal error: resolveRange obtained NONE from one end but SOME from the other"

    fun extractRange (trie, (leftConstraint, rightConstraint)) =
        case trie of
            EMPTY => EMPTY
          | POPULATED n => extractRangeNode (n, leftConstraint, rightConstraint)

    fun enumerateRange (trie, range) =
        foldriRange (fn (k, v, acc) => (k, v) :: acc) [] (trie, range)

    fun foldiPattern' mapFolder f acc (node, p) =
        let fun f' (pfx, item, acc) = f (K.implode pfx, item, acc)
            fun fold' (rpfx, n, xx, acc) =
                case (n, xx) of
                    (LEAF item, []) => f' (rev rpfx, item, acc)
                  | (TWIG (kk, item), []) => acc
                  | (BRANCH (NONE, _), []) => acc
                  | (BRANCH (SOME item, _), []) => f' (rev rpfx, item, acc)
                  | (LEAF _, xx) => acc
                  | (TWIG (kk, item), xx) =>
                    if ListPair.allEq (fn (k, NONE) => true
                                        | (k, SOME x) => k = x)
                                      (K.explode kk, xx)
                    then f' (rev rpfx @ K.explode kk, item, acc)
                    else acc
                  | (BRANCH (_, m), NONE::xs) =>
                    mapFolder (fn (x, n, acc) =>
                                 fold' (x :: rpfx, n, xs, acc))
                             acc m
                  | (BRANCH (_, m), (SOME x)::xs) =>
                    case M.find (m, x) of
                        NONE => acc
                      | SOME nsub => fold' (x :: rpfx, nsub, xs, acc)
        in
            fold' ([], node, p, acc)
        end

    fun foldliPattern f acc (trie, p) =
        case trie of
            EMPTY => acc
          | POPULATED node => foldiPattern' M.foldli f acc (node, p)

    fun foldriPattern f acc (trie, p) =
        case trie of
            EMPTY => acc
          | POPULATED node => foldiPattern' M.foldri f acc (node, p)

    fun enumeratePattern (trie, p) =
        foldriPattern (fn (k, v, acc) => (k, v) :: acc) [] (trie, p)

    fun prefixOf (trie, e) =
        let fun prefix' (n, xx, best, acc) =
                if K.isEmpty xx
                then case n of
                         LEAF item => SOME acc
                       | TWIG (kk, item) => best
                       | BRANCH (NONE, m) => best
                       | BRANCH (SOME item, m) => SOME acc
                else case n of
                         LEAF item => SOME acc
                       | TWIG (kk, item) =>
                         if K.equal (kk, xx) orelse
                            isPrefixOf (K.explode kk, K.explode xx)
                         then SOME (rev (K.explode kk) @ acc)
                         else best
                       | BRANCH (iopt, m) =>
                         let val (x, xs) = (K.head xx, K.tail xx)
                             val best = case iopt of NONE => best
                                                   | SOME _ => SOME acc
                         in
                             case M.find (m, x) of
                                 NONE => best
                               | SOME nsub => prefix' (nsub, xs, best, x::acc)
                         end
        in
            Option.map (K.implode o rev)
                (case trie of
                     EMPTY => NONE
                   | POPULATED node => prefix' (node, e, NONE, []))
        end

end




(* Copyright 2018 Chris Cannam.
   MIT/X11 licence. See the file COPYING for details. *)

signature BIT_VECTOR = sig
    type vector
    val new : int -> vector
    val length : vector -> int
    val tabulate : int * (int -> bool) -> vector
    val sub : vector * int -> bool
    val update : vector * int * bool -> vector
    val foldli : (int * bool * 'a -> 'a) -> 'a -> vector -> 'a
    val foldri : (int * bool * 'a -> 'a) -> 'a -> vector -> 'a
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

    fun tabulate (n : int, f : int -> bool) : Word32.word =
        if (Int.> (n, 32))
        then raise UnsupportedLength
        else
            let fun tabulate' (i, w) =
                    if i = n
                    then w
                    else
                        let val b = f i
                            val updated = if b
                                          then orb (w, bitMask i)
                                          else w
                        in
                            tabulate' (Int.+ (i, 1), updated)
                        end
            in
                tabulate' (0, 0w0)
            end

    fun sub (w : Word32.word, i : int) : bool =
        andb (w, bitMask i) <> 0w0

    fun update (w : Word32.word, i : int, b : bool) : Word32.word =
        if b
        then orb (w, bitMask i)
        else andb (w, notb (bitMask i))

    fun foldli (f : int * bool * 'a -> 'a)
               (acc : 'a)
               (w : Word32.word) : 'a =
        let fun fold' (0w0, w, i, acc) = acc
              | fold' (bit, w, i, acc) =
                fold' (<< (bit, 0w1), w, Int.+ (i, 1),
                       f (i, andb (w, bit) <> 0w0, acc))
        in
            fold' (0w1, w, 0, acc)
        end

    fun foldri (f : int * bool * 'a -> 'a)
               (acc : 'a)
               (w : Word32.word) : 'a =
        let fun fold' (0w0, w, i, acc) = acc
              | fold' (bit, w, i, acc) =
                fold' (>> (bit, 0w1), w, Int.- (i, 1),
                       f (i, andb (w, bit) <> 0w0, acc))
        in
            fold' (0wx80000000, w, 31, acc)
        end

    (* return number of 1s in the first i bits of the word *)
    fun popcount (w : Word32.word, i : int) : int =
        Word32.toInt
            (pc32 (if Int.<(i, 32)
                   then andb (w, bitMask i - 0w1)
                   else w))

    end
end

structure BitVector :> BIT_VECTOR = struct
    local
        fun wordCount n = ((n + 31) div 32)
        fun wordFor i = (i div 32)
        fun bitInWord (iw, i) = (i - iw * 32)
        fun bitsUsed (iw, n) = let val bn = bitInWord (iw, n)
                               in if bn > 32 then 32 else bn
                               end

    in
        type vector = int * BitWord32.vector vector
        exception UnsupportedLength

        fun new n : vector =
            (n, Vector.tabulate (wordCount n, fn _ => BitWord32.new 32))

        fun length ((n, _) : vector) : int =
            n

        fun tabulate (n : int, f : int -> bool) : vector =
            (n, Vector.tabulate
                    (wordCount n,
                     fn iw => BitWord32.tabulate (bitsUsed (iw, n),
                                                  fn ib => f (iw * 32 + ib))))

        fun sub ((n, vec) : vector, i : int) : bool =
            if i >= n
            then raise Subscript
            else
                let val iw = wordFor i
                in
                    BitWord32.sub (Vector.sub (vec, iw), bitInWord (iw, i))
                end

        fun update ((n, vec) : vector, i : int, b : bool) : vector =
            if i >= n
            then raise Subscript
            else
                let val iw = wordFor i
                in
                    (n, Vector.update
                            (vec, iw,
                             BitWord32.update (Vector.sub (vec, iw),
                                               bitInWord (iw, i),
                                               b)))
                end

        fun fold' vectorFold bitwordFold f acc (n, vec) =
            vectorFold (fn (iw, w, acc) =>
                           bitwordFold (fn (ib, b, acc) =>
                                           let val i = iw * 32 + ib
                                           in
                                               if i >= n
                                               then acc
                                               else f (i, b, acc)
                                           end)
                                       acc
                                       w)
                       acc
                       vec

        fun foldli (f : (int * bool * 'a -> 'a))
                   (acc : 'a)
                   (v : vector) : 'a =
            fold' Vector.foldli BitWord32.foldli f acc v

        fun foldri (f : (int * bool * 'a -> 'a))
                   (acc : 'a)
                   (v : vector) : 'a =
            fold' Vector.foldri BitWord32.foldri f acc v

        (* population count: return number of 1s in the first i bits
           of the vector *)
        fun popcount ((n, vec) : vector, i : int) : int =
            let val iw = wordFor i
            in
                Vector.foldli
                    (fn (j, w, acc) =>
                        if j > iw
                        then acc
                        else if j < iw
                        then acc + BitWord32.popcount (w, 32)
                        else acc + BitWord32.popcount (w, bitInWord (j, i)))
                    0 vec
            end
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

    fun tabulate (n : int, f : int -> 'a option) : 'a vector =
        let val expanded = Vector.tabulate (n, f)
        in
            (V.tabulate
                 (n, fn i => Option.isSome (Vector.sub (expanded, i))),
             Vector.fromList
                 (List.concat
                      (List.tabulate
                           (n, fn i => case Vector.sub (expanded, i) of
                                           NONE => []
                                         | SOME x => [x]))))
        end

    fun contains ((b, _) : 'a vector, i : int) : bool =
        V.sub (b, i)

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

    fun enumerate (vec as (b, v) : 'a vector) : 'a option list =
        V.foldri
            (fn (i, b, acc) =>
                (if b
                 then SOME (sub (vec, i))
                 else NONE)
                :: acc)
            [] b

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

    fun mapi (f : int * 'a -> 'b) ((b, v) : 'a vector) : 'b vector =
        (b,
         let val i = ref (~1)
             fun advance () =
                 (i := ! i + 1;
                  if V.sub (b, ! i) then ()
                  else advance ())
         in
             Vector.mapi (fn (ix, x) => (advance (); f (! i, x))) v
         end)

    fun map (f : 'a -> 'b) ((b, v) : 'a vector) : 'b vector =
        (b, Vector.map f v)

    fun foldli (f : (int * 'a * 'b -> 'b))
               (acc : 'b) ((b, v) : 'a vector) : 'b =
        case V.foldli
                 (fn (i, bit, (ix, acc)) =>
                     if bit
                     then (ix+1, f (i, Vector.sub (v, ix), acc))
                     else (ix, acc))
                 (0, acc) b of
            (ix, acc) => acc

    fun foldri (f : (int * 'a * 'b -> 'b))
               (acc : 'b) ((b, v) : 'a vector) : 'b =
        case V.foldri
                 (fn (i, bit, (ix, acc)) =>
                     if bit
                     then (ix-1, f (i, Vector.sub (v, ix-1), acc))
                     else (ix, acc))
                 (Vector.length v, acc) b of
            (ix, acc) => acc

    (* foldl/foldr are simpler than foldli/foldri, as they don't need
       to look at the bitmap at all *)
    fun foldl (f : ('a * 'b -> 'b))
              (acc : 'b) ((_, v) : 'a vector) : 'b =
        Vector.foldl f acc v

    fun foldr (f : ('a * 'b -> 'b))
              (acc : 'b) ((_, v) : 'a vector) : 'b =
        Vector.foldr f acc v

end

structure BitMappedVector = BitMappedVectorFn(BitVector)
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
    val keyCompare = Int.compare

end

signature WORD32_TRIE_MAP_FN_ARG = sig
    val bitsToUse : int
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
        val valuesPerNode = Word.toInt (Word.<< (0w1, bitsPerNodeW))
        val maskShift = 0w32 - bitsPerNodeW
        val nodesPerWord = Int.quot (32, bitsPerNode) +
                           (case Int.mod (32, bitsPerNode) of
                                0 => 0
                              | _ => 1)
        val bitsInLastNodeW = case Int.mod (32, bitsPerNode) of
                                  0 => bitsPerNodeW
                                | n => Word.fromInt n

        type element = int
        type key = Word32.word
        fun isEmpty w = w = Word32.fromInt 0
        fun head w = Word32.toIntX (Word32.>> (w, maskShift))
        fun tail w = Word32.<< (w, bitsPerNodeW)
        fun explode k = if isEmpty k then []
                        else head k :: explode (tail k)
        fun implode xx =
            let fun implode' (xx, i, acc) =
                    if i + 1 = nodesPerWord
                    then case xx of
                             [] => Word32.<< (acc, bitsInLastNodeW)
                           | x::xs =>
                             Word32.orb (Word32.<< (acc, bitsInLastNodeW),
                                         Word32.>> (Word32.fromInt x,
                                                    bitsPerNodeW -
                                                    bitsInLastNodeW))
                    else case xx of
                             [] =>
                             implode' (xx, i + 1,
                                       Word32.<< (acc, bitsPerNodeW))
                           | x::xs =>
                             implode' (xs, i + 1,
                                       Word32.orb
                                           (Word32.<< (acc, bitsPerNodeW),
                                            Word32.fromInt x))
            in
                implode' (xx, 0, 0w0)
            end
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



signature PERSISTENT_ARRAY = sig

    type 'a array (* nb not an eqtype *)

    (* I. Functions identical to ARRAY *)

    val maxLen : int
    val array : int * 'a -> 'a array
    val fromList : 'a list -> 'a array
    val tabulate : int * (int -> 'a) -> 'a array
    val length : 'a array -> int
    val sub : 'a array * int -> 'a
    val vector : 'a array -> 'a Vector.vector
    val app : ('a -> unit) -> 'a array -> unit
    val appi : (int * 'a -> unit) -> 'a array -> unit
    val foldl : ('a * 'b -> 'b) -> 'b -> 'a array -> 'b
    val foldli : (int * 'a * 'b -> 'b) -> 'b -> 'a array -> 'b
    val foldr : ('a * 'b -> 'b) -> 'b -> 'a array -> 'b
    val foldri : (int * 'a * 'b -> 'b) -> 'b -> 'a array -> 'b
    val find : ('a -> bool) -> 'a array -> 'a option
    val findi : (int * 'a -> bool) -> 'a array -> (int * 'a) option
    val exists : ('a -> bool) -> 'a array -> bool
    val all : ('a -> bool) -> 'a array -> bool
    val collate : ('a * 'a -> order) -> 'a array * 'a array -> order

    (* II. Functions similar to ARRAY, but altered for a persistent
           array. The functions passed to modify/modifyi should return
           NONE for "no change" or SOME x to change the value. *)

    val update : 'a array * int * 'a -> 'a array
    val modify : ('a -> 'a option) -> 'a array -> 'a array
    val modifyi : (int * 'a -> 'a option) -> 'a array -> 'a array

    (* III. Functions not in ARRAY *)

    val toList : 'a array -> 'a list
    val map : ('a -> 'b) -> 'a array -> 'b array
    val mapi : (int * 'a -> 'b) -> 'a array -> 'b array
    val empty : 'a array
    val isEmpty : 'a array -> bool
    val append : 'a array * 'a -> 'a array
    val popEnd : 'a array -> 'a array * 'a
    val peekEnd : 'a array -> 'a

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

    fun isEmpty (A { size, trie } : 'a array) =
        size = 0w0

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

    fun peekEnd (A { size, trie }) =
        case T.find (trie, size - 0w1) of
            NONE => raise Empty
          | SOME x => x

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

    fun foldl f acc (A { size, trie }) =
        T.foldl f acc trie

    fun foldli f acc (A { size, trie }) =
        (* T.foldli is much slower than T.foldl, because it has to reconstruct
           the keys as it goes. It's quicker for us just to count them *)
        case T.foldl (fn (x, (i, acc)) => (i + 1, f (i, x, acc)))
                     (0, acc) trie of
            (_, acc) => acc

    fun foldr f acc (A { size, trie }) =
        T.foldr f acc trie

    fun foldri f acc (A { size, trie }) =
        (* as foldli *)
        case T.foldr (fn (x, (i, acc)) => (i - 1, f (i, x, acc)))
                     (Word32.toInt size - 1, acc) trie of
            (_, acc) => acc

    fun find f (A { size, trie }) =
        T.search f trie

    fun findi f (A { size, trie }) =
        Option.map (fn (w, x) => (Word32.toInt w, x))
                   (T.searchi (fn (w, x) => f (Word32.toInt w, x)) trie)

    fun exists f (A { size, trie }) =
        Option.isSome (T.search f trie)

    fun all f (A { size, trie }) =
        not (Option.isSome (T.search (fn x => not (f x)) trie))

    fun mapi f v =
        foldli (fn (i, x, acc) => append (acc, f (i, x))) empty v

    fun map f (A { size, trie }) =
        A { size = size, trie = T.map f trie }

    fun appi f v =
        foldli (fn (i, x, _) => ignore (f (i, x))) () v

    fun app f v =
        foldl (fn (x, _) => ignore (f x)) () v

    fun fromList xx =
        List.foldl (fn (x, acc) => append (acc, x)) empty xx

    fun tabulate (n, f) =
        let fun tabulate' (i, v) =
                if i = n
                then v
                else tabulate' (i + 1, append (v, f i))
        in
            tabulate' (0, empty)
        end

    fun toList v =
        foldr (op::) [] v

    fun vector v =
        Vector.fromList (toList v)

    fun modifyi f v =
        foldli (fn (i, x, updating) =>
                   case f (i, x) of
                       NONE => updating
                     | SOME x' => update (updating, i, x'))
               v v

    fun modify f v =
        modifyi (fn (i, x) => f x) v

    fun collate f (v1, v2) =
        let val len1 = length v1
            val len2 = length v2
            fun collate' i =
                if i = len1
                then if i = len2
                     then EQUAL
                     else LESS
                else if i = len2
                then GREATER
                else case f (sub (v1, i), sub (v2, i)) of
                         EQUAL => collate' (i+1)
                       | order => order
        in
            collate' 0
        end

    fun array (n, x) =
        tabulate (n, fn _ => x)

end

structure PersistentArray : PERSISTENT_ARRAY = PersistentArrayImpl
