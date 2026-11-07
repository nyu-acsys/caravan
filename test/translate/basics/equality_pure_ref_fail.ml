let compare_refs (left : int ref) (right : int ref) = left = right
(*@ result = compare_refs left right pure ensures result = false *)
