val succ : int -> int
(*@ result = succ x requires x < 100 ensures result = x + 1 *)
