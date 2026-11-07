(* Functions that contracts call are pure: each is also a function that contracts can
   use, whose value its code computes. *)

type tree = Leaf | Node of tree * int * tree

(* The postcondition holds of the function too, which gives the bound on the subtrees. *)
let rec size t = match t with Leaf -> 0 | Node (l, _, r) -> size l + 1 + size r
(*@ n = size t
    requires size t < 1000
    ensures n >= 0 *)

let rec all_small l =
  match l with [] -> true | x :: t -> 0 <= x && x <= 1000 && all_small t
(*@ b = all_small l *)

let rec sum (l : int list) = match l with [] -> 0 | x :: t -> x + sum t
(*@ s = sum l
    requires all_small l
    requires List.length l <= 1000
    ensures 0 <= s <= 1000 * List.length l *)

let max (a : int) b = if a >= b then a else b

let rec height t =
  match t with Leaf -> 0 | Node (l, _, r) -> 1 + max (height l) (height r)
(*@ h = height t
    requires size t < 1000
    ensures 0 <= h <= size t *)

(* Contracts using pure functions, of functions that are not pure. *)
let grow t x = Node (t, x, Leaf)
(*@ r = grow t x
    requires size t < 999
    ensures size r = size t + 1
    ensures height r = 1 + height t *)

let double_sum (l : int list) =
  let s = sum l in
  s + s
(*@ d = double_sum l
    requires all_small l
    requires List.length l <= 1000
    ensures d = 2 * sum l *)
