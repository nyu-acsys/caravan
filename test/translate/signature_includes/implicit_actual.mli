type t

(*@ predicate chosen (x : t) (copy [@implicit] : t) *)

val get : t -> t
(*@ result = get x requires chosen x copy ensures chosen x copy && result === copy *)

val again : t -> t
(*@ result = again x requires chosen x copy ensures chosen x copy && result === copy *)
