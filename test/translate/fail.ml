(* Each of these fails, with the error at the OCaml code. *)

let wrong x = x + 1
(*@ r = wrong x
    requires x < max_int
    ensures r = x *)

let pred n = n - 1
(*@ r = pred n
    requires n > 0
    ensures r >= 0 *)

let caller x = pred x
let unchecked x = assert (x > 0)
