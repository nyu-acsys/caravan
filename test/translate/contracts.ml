(* Contracts in Gospel's syntax: the header names the arguments and the result. *)

let clamp (x : int) lo hi = if x < lo then lo else if x > hi then hi else x
(*@ r = clamp v a b
    requires a <= b
    ensures a <= r <= b
    ensures a <= v <= b -> r = v
    ensures (r = v) <-> (a <= v /\ v <= b) *)

let is_even n = n mod 2 = 0
(*@ b = is_even n
    ensures b <-> exists k: int. n = 2 * k
    ensures not b -> n mod 2 <> 0 *)

let succ_pos n = n + 1
(*@ r = succ_pos n
    requires 0 <= n < max_int
    ensures forall m: int. 0 <= m <= n -> m < r *)

(* A variable of type int ranges over the values of OCaml's int. *)
let top () = max_int
(*@ r = top ()
    ensures forall m: int. m <= r *)
