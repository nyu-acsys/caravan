exception Empty
exception Bad of int

let check n = if n < 0 then raise (Bad n) else if n = 0 then raise Empty else n
(*@ r = check n
    raises Bad m -> m < 0 *)
