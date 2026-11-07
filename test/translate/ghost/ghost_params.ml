(* Ghost parameters, which calls find from the preconditions that relate them to
   arguments. *)

type pair = { a : int Atomic.t; b : int Atomic.t }

let read (a : int Atomic.t) = Atomic.get a
(*@ r = read [p : pair] a
    requires a == p.a
    requires own p.a n
    ensures own p.a n && r = n *)

let get { a; _ } = read a
(*@ r = get p
    requires own p.a n
    ensures own p.a n && r = n *)
