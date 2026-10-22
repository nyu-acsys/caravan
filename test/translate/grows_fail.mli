type t

(*@ predicate is_counter (c : t) [@persistent] *)

val create : unit -> t
(*@ c = create ()
    ensures is_counter c *)
