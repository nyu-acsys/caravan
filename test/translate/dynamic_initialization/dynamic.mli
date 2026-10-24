type t

(*@ invariant valid (q : t) *)
val empty : unit -> t

(*@ q = empty () ensures valid q *)
val singleton : unit -> t

(*@ q = singleton () ensures valid q *)
val pair : unit -> t
(*@ q = pair () ensures valid q *)
