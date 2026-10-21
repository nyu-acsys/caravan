(* A match OCaml finds not exhaustive, and a wrong contract. *)

type shape = Circle of int | Rect of int * int | Empty

let radius s = match s with Circle r -> r
(*@ r = radius s *)

let width s = match s with Rect (w, _) -> w | _ -> 0
(*@ w = width s
    ensures w > 0 *)
