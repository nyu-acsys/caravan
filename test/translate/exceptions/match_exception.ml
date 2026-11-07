exception Empty

let head (xs : int list) = match xs with [] -> raise Empty | x :: _ -> x
(*@ r = head xs
    ensures match xs with [] -> false | x :: _ -> r = x
    raises Empty -> xs = [] *)

let describe xs = match head xs with exception Empty -> 0 | 0 -> 1 | _ -> 2
(*@ r = describe xs
    ensures xs = [] -> r = 0
    ensures (match xs with [] -> false | x :: _ -> x = 0) -> r = 1 *)

(* A value case's own exception is not caught by the match. *)
let again xs ys = match head xs with exception Empty -> 0 | _ -> head ys
(*@ r = again xs ys
    raises Empty -> xs <> [] && ys = [] *)
