exception Empty
exception Bad of int

let head (xs : int list) = match xs with [] -> raise Empty | x :: _ -> x
(*@ r = head xs
    raises Empty -> xs = [] *)

let check n = if n < 0 then raise (Bad n) else n
(*@ r = check n
    raises Bad m -> m < 0 *)

(* Empty escapes the handler, but the contract does not say so. *)
let first_checked xs = try check (head xs) with Bad _ -> 0
(*@ r = first_checked xs *)
