type t

(*@ invariant shared (x : t) *)
(*@ invariant other (x : t) *)
(*@ invariant versioned (x : t) (version : int) *)

val touch : t -> unit
(*@ touch x requires shared x ensures shared x *)

val touch_version : t -> int -> unit
(*@ touch_version x version requires versioned x version ensures versioned x version *)
