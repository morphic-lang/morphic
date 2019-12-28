; data, capacity, length
%type.flat = type { i32*, i64, i64 }

define i32* @flat_get_data(%type.flat* %flat_ref)
{
    %data_ref = getelementptr inbounds %type.flat, %type.flat* %flat_ref, i32 0, i32 0
    %data = load i32*, i32** %data_ref
    ret i32* %data
}

define i64 @flat_get_cap(%type.flat* %flat_ref)
{
    %cap_ref = getelementptr inbounds %type.flat, %type.flat* %flat_ref, i32 0, i32 1
    %cap = load i64, i64* %cap_ref
    ret i64 %cap
}

define i64 @flat_get_len(%type.flat* %flat_ref)
{
    %len_ref = getelementptr inbounds %type.flat, %type.flat* %flat_ref, i32 0, i32 2
    %len = load i64, i64* %len_ref
    ret i64 %len
}

define void @flat_resize(%type.flat* %flat_ref, i32 %item)
{
    ; TODO
    ret void
}

define void @flat_push(%type.flat* %flat_ref, i32 %item)
{
    %len = call i64 @flat_get_len(%type.flat* %flat_ref)
    %cap = call i64 @flat_get_cap(%type.flat* %flat_ref)
    %should_resize = icmp eq i64 %len, %cap
    br i1 %should_resize, label %Resize, label %Push

Resize:
    ; Do the resize
    ret void

Push:
    ; Do the push
    ret void
}