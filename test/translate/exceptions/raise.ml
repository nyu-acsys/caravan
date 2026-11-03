exception Empty
exception Bad of int

let head (xs : int list) = match xs with [] -> raise Empty | x :: _ -> x
(*@ r = head xs
    ensures match xs with [] -> false | x :: _ -> r = x
    raises Empty -> xs = [] *)

let check n = if n < 0 then raise (Bad n) else n
(*@ r = check n
    ensures r = n && n >= 0
    raises Bad m -> m = n && n < 0 *)

let first_checked xs = check (head xs)
(*@ r = first_checked xs
    ensures r >= 0
    raises Empty -> xs = []
    raises Bad m -> m < 0 *)
