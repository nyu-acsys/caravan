(** Trusted constants from [Stdlib.Int]. *)

val max_int : int
(*@ result = max_int ensures result === max_int *)

val min_int : int
(*@ result = min_int ensures result === min_int *)
