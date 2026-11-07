val incr : int -> int
(*@ r = incr x
    requires x < max_int
    ensures r = x + 1 *)
