type t

(*@ invariant shared (c : t) *)
(*@ predicate cell (c : t) (value : int) *)

val make : int -> t
(*@ c = make value
    ensures shared c && cell c value *)
