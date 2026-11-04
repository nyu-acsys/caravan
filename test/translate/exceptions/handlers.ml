exception Empty
exception Bad of int

let head (xs : int list) = match xs with [] -> raise Empty | x :: _ -> x
(*@ r = head xs
    ensures match xs with [] -> false | x :: _ -> r = x
    raises Empty -> xs = [] *)

let check n = if n < 0 then raise (Bad n) else n
(*@ r = check n
    ensures r = n && n >= 0
    raises Bad m -> m = n && n < 0 *)

(* A handler catching everything: no raises clause needed. *)
let head_or xs d = try head xs with Empty -> d
(*@ r = head_or xs d
    ensures match xs with [] -> r = d | x :: _ -> r = x *)

(* The rest of a protected sequence does not run after a raise. *)
let min2 xs ys =
  try
    let a = head xs in
    let b = head ys in
    if a < b then a else b
  with Empty -> 0
(*@ r = min2 xs ys
    ensures (xs = [] || ys = []) -> r = 0 *)

(* A payload binding, and an exception the handler does not catch propagating. *)
let checked_head xs = try check (head xs) with Bad m -> if m < 0 then 0 else 1
(*@ r = checked_head xs
    ensures r = 0 || (match xs with [] -> false | x :: _ -> r = x && x >= 0)
    raises Empty -> xs = [] *)

(* Nested handlers, and re-raising what a handler caught. *)
let nested xs = try try check (head xs) with Bad _ -> 0 with e -> raise e
(*@ r = nested xs
    ensures r >= 0
    raises Empty -> xs = [] *)
