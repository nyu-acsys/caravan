type 'a t

(*@ invariant is_cell (q : 'a t) *)
(*@ predicate cell (q : 'a t) (value : 'a * int) *)

val checked : unit -> unit
