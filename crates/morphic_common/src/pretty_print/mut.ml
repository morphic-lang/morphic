module MutArrayImpl = struct
    type 'a elem
        = FULL of 'a
        | VACANT

    type 'a array = A of {
        len : int;
        data : 'a elem Array.t
    }

    let length (A { len; data }) =
        len

    let append (A { len; data }, x) =
        let
            newData =
                if len + 1 >= Array.length data
                then
                    let
                        newCap = if Array.length data > 0 then (Array.length data) * 2 else 4
                        in let newData = Array.make newCap VACANT
                        in let _ = Array.blit data 0 newData 0 len
                    in
                        newData
                else
                    data

        in let _ = Array.set newData len (FULL x)
        in
            A { len = len + 1; data = newData }

    let popEnd (A { len; data }) =
        if len > 0
        then
            let
                x =
                    match Array.get data (len - 1) with
                          FULL x -> x
                        | VACANT ->
                            raise (Invalid_argument "popEnd Subscript exception")
                in let _ = Array.set data (len - 1) VACANT
            in
                (A { len = len - 1; data = data }, x)
        else
            raise Stack.Empty

    let sub (A { len; data }, i) =
        match Array.get data i with
              VACANT ->
                raise (Invalid_argument "sub Subscript exception")
            | FULL x -> x

    let update (A { len; data }, i, x) =
        if i < 0 || i >= len
        then
            raise (Invalid_argument "update Subscript exception")
        else
            let _ = Array.set data i (FULL x) in
                A { len = len; data = data }

    let fromList xx =
        let data = Array.map (fun x -> FULL x) xx in
            A { len = Array.length data; data = data }

    let toList (A { len; data }) =
        Array.fold_right
            (fun x xx ->
                match x with
                      FULL x -> (x :: xx)
                    | VACANT ->
                        raise (Invalid_argument "toList Subscript exception")
            )
            data
            []
end

module PersistentArray = MutArrayImpl
