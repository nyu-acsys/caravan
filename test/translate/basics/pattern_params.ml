(* Parameters that are patterns, named as the contract names them. *)

type pair = { a : int Atomic.t; b : int Atomic.t }

let get_a { a; _ } = Atomic.get a
(*@ r = get_a p
    requires own p.a n
    ensures own p.a n && r = n *)

let swap ((x : int), (y : bool)) = (y, x)
(*@ r = swap xy
    ensures match xy with (x, y) -> r = (y, x) *)
