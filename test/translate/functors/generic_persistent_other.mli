type t

(*@ invariant shared (x : t) *)

val touch : t -> unit
(*@ touch x requires shared x ensures shared x *)
