(* Lists and options, and the functions on lists that contracts can use. *)

let rec length (l : int list) = match l with [] -> 0 | _ :: t -> 1 + length t
(*@ n = length l
    requires List.length l < max_int
    ensures n = List.length l *)

let rec append (l1 : int list) l2 = match l1 with [] -> l2 | x :: t -> x :: append t l2
(*@ l = append l1 l2
    ensures l = l1 @ l2
    ensures List.length l = List.length l1 + List.length l2 *)

let head_opt (l : int list) = match l with [] -> None | x :: _ -> Some x
(*@ r = head_opt l
    ensures match l with [] -> r = None | x :: _ -> r = Some x *)

let rec mem (x : int) l = match l with [] -> false | y :: t -> x = y || mem x t
(*@ b = mem x l
    ensures b <-> List.mem x l *)

(* A nested pattern on a list, and an option of a list. *)
let second (l : int list) = match l with _ :: y :: _ -> Some [ y ] | _ -> None
(*@ r = second l
    ensures match l with _ :: y :: _ -> r = Some [y] | _ -> r = None *)

let rec sum_opt (l : int option list) =
  match l with
  | [] -> 0
  | Some x :: t -> if x > 0 && x < 1000 then x + sum_opt t else sum_opt t
  | None :: t -> sum_opt t
(*@ s = sum_opt l
    requires List.length l < 1000
    ensures 0 <= s < 1000 * (List.length l + 1) *)
