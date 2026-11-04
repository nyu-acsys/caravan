exception Empty
exception Bad of int

let head (xs : int list) = match xs with [] -> raise Empty | x :: _ -> x
(*@ r = head xs
    raises Empty -> xs = [] *)

(* Re-raising what was caught raises Empty, which the contract does not declare. *)
let first xs = try head xs with e -> raise e
(*@ r = first xs
    raises Bad m -> m < 0 *)
