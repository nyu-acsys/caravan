(* Variant types, tuples and pattern matching. *)

type shape = Circle of int | Rect of int * int | Empty

(* Flat cases become a Raven match. *)
let area s = match s with Circle r -> 3 * r * r | Rect (w, h) -> w * h | Empty -> 0
(*@ a = area s
    requires match s with
             | Circle r -> 0 <= r <= 1000
             | Rect (w, h) -> 0 <= w <= 1000 && 0 <= h <= 1000
             | Empty -> true
    ensures a >= 0 *)

type tree = Leaf | Node of tree * int * tree

let singleton x = Node (Leaf, x, Leaf)
(*@ t = singleton x
    ensures t = Node (Leaf, x, Leaf) *)

(* A nested pattern, and a variable matching the rest. *)
let root_or_zero t =
  match t with Node (Leaf, x, Leaf) -> x | Node (_, x, _) -> x + 0 | other -> 0
(*@ r = root_or_zero t
    ensures match t with Node (_, x, _) -> r = x | Leaf -> r = 0 *)

(* Tuples, and an or-pattern. *)
let swap (p : int * int) = match p with a, b -> (b, a)
(*@ q = swap p
    ensures match q with (b, a) -> p = (a, b) *)

let is_small s = match s with Empty | Circle 0 -> true | _ -> false
(*@ b = is_small s
    ensures b <-> (s = Empty || s = Circle 0) *)

let left t = match t with Node (l, _, _) -> l | Leaf -> Leaf
(*@ l = left t
    ensures t = Leaf -> l = Leaf *)
