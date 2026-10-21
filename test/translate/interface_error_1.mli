type t

(*@ predicate is_lock (l : t) (b : bool) *)

val create : unit -> t
(*@ l = create ()
    ensures is_lock l false *)
