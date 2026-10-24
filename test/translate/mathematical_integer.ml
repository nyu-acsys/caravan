let anchor () = ()
(*@ anchor ()
    ensures exists value : integer. value = max_int + 1
    ensures forall value : int. min_int <= value && value <= max_int *)
