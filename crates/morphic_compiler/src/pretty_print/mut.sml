structure MutArrayImpl = struct
    datatype 'a elem
        = FULL of 'a
        | VACANT

    datatype 'a array = A of {
        len : int,
        data : 'a elem Array.array
    }

    fun length (A { len, data }) =
        len

    fun append (A { len, data }, x) =
        let
            val newData =
                if len + 1 >= Array.length data
                then
                    let
                        val newCap = if Array.length data > 0 then (Array.length data) * 2 else 4
                        val newData = Array.array (newCap, VACANT)
                        val _ = Array.copy {
                            src = data,
                            dst = newData,
                            di = 0
                        }
                    in
                        newData
                    end
                else
                    data

            val _ = Array.update (newData, len, FULL x)
        in
            A { len = len + 1, data = newData }
        end

    fun popEnd (A { len, data }) =
        if len > 0
        then
            let
                val x =
                    case Array.sub (data, len - 1) of
                          FULL x => x
                        | VACANT =>
                            let val _ = print "popEnd Subscript exception" in
                                raise Subscript
                            end

                val _ = Array.update (data, len - 1, VACANT)
            in
                (A { len = len - 1, data = data }, x)
            end
        else
            raise Empty

    fun sub (A { len, data }, i) =
        case Array.sub (data, i) of
              VACANT =>
                let val _ = print "sub Subscript exception" in
                    raise Subscript
                end
            | FULL x => x

    fun update (A { len, data }, i, x) =
        if i < 0 orelse i >= len
        then
            let val _ = print "update Subscript exception" in
                raise Subscript
            end
        else
            let val _ = Array.update (data, i, FULL x) in
                A { len = len, data = data }
            end

    fun fromList xx =
        let val data = Array.fromList (List.map FULL xx) in
            A { len = Array.length data, data = data }
        end

    fun toList (A { len, data }) =
        ArraySlice.foldr
            (fn (x, xx) =>
                case x of
                      FULL x => (x :: xx)
                    | VACANT =>
                        let val _ = print "toList Subscript exception" in
                            raise Subscript
                        end
            )
            []
            (ArraySlice.slice (data, 0, SOME len))
end

structure PersistentArray = MutArrayImpl
