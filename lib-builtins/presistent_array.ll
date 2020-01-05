; data, sidecar, length, refcount
%type.root = type { [256 x i8], %struct.leaf*, i64, i64 }

; data, refcount
%type.branch = type { [32 x i8*], i64 }

; data, refcount
%type.leaf = type { [256 x i8], i64 }

define i64* @get_root_refcount(%type.root* %root_ref)
{
    %refcount_ref = getelementptr inbounds %type.root, %type.root* %root_ref, i64 0, i64 3
    ret i64* %refcount_ref
}

define i64* @get_root_len(%type.root* %root_ref)
{
    %len_ref = getelementptr inbounds %type.root, %type.root* %root_ref, i64 0, i64 2
    ret i64* %len_ref
}

define i64* @get_branch_refcount(%type.branch* %branch_ref)
{
    %refcount_ref = getelementptr inbounds %type.branch, %type.branch* %branch_ref, i64 0, i64 1
    ret i64* %refcount_ref
}

define i64* @get_leaf_refcount(%type.leaf %leaf_ref)
{
    %refcount_ref = getelementptr inbounds %type.leaf, %type.leaf* %leaf_ref, i64 0, i64 1
}

define void @inc64(i64* %i_ref)
{
    %old_i = load i64, i64* %i_ref
    %new_i = add i64 %old_i, 1
    store i64 %new_i, i64* %i_ref
    ret void
}

define i1 @dec64_checkz(i64* %i_ref)
{
    %old_i = load i64, i64* %i_ref
    %new_i = sub i64 %old_1, 1
    store i64 %new_i, i64* %i_ref
    %check = icmp eq i64 %new_i, 0
    ret i1 %check
}

define void @retain(%type.root* %root_ref)
{
    %refcount_ref = call i64* @get_root_refcount(%type.root* %root_ref)
    call void @inc64(i64* %refcount_ref)
    ret void
}

define i1 @is_inline(%type.root* %root_ref)
{
    ; Assumes items are i8s
    %len_ref = call i64* @get_root_len(%type.root* %root_ref)
    %len = load i64, i64* %len_ref
    %result = icmp ule i64 %len, 256
    ret i1 %result
}

define void @release_branch(%type.branch* %branch_ref, i64 %len)
{
    %refcount_ref = call i64* @get_branch_refcount(%type.branch* %branch_ref)
    %should_free = call i1 @dec64_checkz(i64* %refcount_ref)
    br i1 %should_free, label %Free, label %Done

Free:
    ; TODO
    ret void
}

define void @release(%type.root* %root_ref)
{
    %refcount_ref = call i64* @get_root_refcount(%type.root* %root_ref)
    %should_free = call i1 @dec64_checkz(i64* %refcount_ref)
    br i1 %should_free, label %Free, label %Done

Free:
    %inline = call i1 @is_inline(%type.root* %root_ref)
    br i1 %inline, label %FreeFinal, label %FreeRecurse

FreeRecurse:


FreeFinal:
    ; free call
    ret void

Done:
    ret void
}