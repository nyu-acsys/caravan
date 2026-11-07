exception Empty
exception Bad of int

let make n = if n > 0 then Bad n else Empty
(*@ e = make n
    ensures if n > 0 then e = Bad n else e = Empty *)

let code e = match e with Bad n -> n | Empty -> 0 | _ -> -1
(*@ r = code e
    ensures e = Empty -> r = 0 *)
