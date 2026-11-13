val good : int -> int
(*@ result = good value pure ensures result === value *)

val bad : int -> int
(*@ result = bad value pure ensures result === value + 1 *)
