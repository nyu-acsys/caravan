type t

(*@ predicate owned (x : t) (n [@implicit] : int) *)
(*@ invariant shared (x : t) *)

val read : t -> int
(*@ result = read x requires owned x n && shared x ensures owned x n && shared x && result = n *)

val again : t -> int
(*@ result = again x requires owned x n && shared x ensures owned x n && shared x && result = n *)
