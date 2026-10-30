type t

(*@ invariant is_counter (c : t) *)

val create : unit -> t
(*@ c = create ()
    ensures is_counter c *)
