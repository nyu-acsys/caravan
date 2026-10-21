(* First-order functions on integers and booleans, with their contracts. *)

let abs x = if x < 0 then -x else x
(*@ r = abs x
    requires x > min_int
    ensures r >= 0
    ensures r = x || r = -x *)

let max (a : int) (b : int) = if a >= b then a else b
(*@ m = max a b
    ensures m >= a && m >= b *)

let rec sum n = if n = 0 then 0 else n + sum (n - 1)
(*@ s = sum n
    requires 0 <= n && n <= 1000
    ensures n <= s && s <= 1000 * n *)

(* A call in the right operand of && is made only if the left one holds. *)
let small_sum n = n >= 0 && n <= 1000 && sum n >= 0
(*@ b = small_sum n
    ensures b = (n >= 0 && n <= 1000) *)

let double x =
  let y = x + x in
  assert (y = 2 * x);
  y
(*@ r = double x
    requires min_int / 2 <= x && x <= max_int / 2
    ensures r = 2 * x *)

let check x = if x > min_int then assert (abs x >= 0)
