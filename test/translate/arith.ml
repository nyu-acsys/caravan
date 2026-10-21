(* First-order functions on integers and booleans, with their contracts. *)

let abs x = if x < 0 then -x else x
(*@ r = abs x
    ensures r >= 0
    ensures r = x || r = -x *)

let max (a : int) (b : int) = if a >= b then a else b
(*@ m = max a b
    ensures m >= a && m >= b *)

let rec sum n = if n = 0 then 0 else n + sum (n - 1)
(*@ s = sum n
    requires n >= 0
    ensures s >= n *)

(* A call in the right operand of && is made only if the left one holds. *)
let positive_sum n = n >= 0 && sum n >= 0
(*@ b = positive_sum n
    ensures b = (n >= 0) *)

let double x =
  let y = x + x in
  assert (y = 2 * x);
  y
(*@ r = double x
    ensures r = 2 * x *)

let check x = assert (abs x >= 0)
