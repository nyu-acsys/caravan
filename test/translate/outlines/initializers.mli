type t

(*@ invariant shared (c : t) *)
(*@ predicate cell (c : t) (value : int) *)

val make : int -> t
(*@ c = make value ensures shared c && cell c value *)

val zero : unit -> t
(*@ c = zero () ensures shared c && cell c 0 *)
