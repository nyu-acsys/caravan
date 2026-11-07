type pair = { a : int Atomic.t; b : int Atomic.t }

let read (a : int Atomic.t) = Atomic.get a
(*@ r = read [p : pair] a
    requires a == p.a
    requires own p.a n
    ensures own p.a n && r = n *)

(* Nothing relates the argument to a pair. *)
let read_fresh () = read (Atomic.make 0)
