(* OCaml's int is 63 bits, and its division rounds towards zero. *)

let half x = x / 2
(*@ r = half x
    ensures r = x / 2
    ensures x >= 0 || r <= 0 *)

let neg_rounding () = assert (-7 / 2 = -3 && -7 mod 2 = -1)
let safe_incr x = x + 1
(*@ r = safe_incr x
    requires x < 4611686018427387903
    ensures r = x + 1 *)

(* These fail: each may overflow, and div may divide by zero. *)

let incr x = x + 1
let div x y = x / y
let safe_div x y = x / y
(*@ r = safe_div x y
    requires y > 0 *)

let neg x = -x
