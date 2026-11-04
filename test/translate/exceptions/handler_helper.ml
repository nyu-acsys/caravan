exception Empty

let head (xs : int list) = match xs with [] -> raise Empty | x :: _ -> x
(*@ r = head xs
    raises Empty -> xs = [] *)

(* A helper whose handler catches everything does not raise. *)
let safe xs = try head xs with _ -> 0
let user xs = safe xs
(*@ r = user xs *)
