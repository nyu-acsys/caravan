(* A contract that matches on the witness, which the wrappers rely on. *)

type ('a, _) poly =
  | Option : ('a, 'a option) poly
  | Value : ('a, 'a) poly
  | Unit : ('a, unit) poly

let first : type a r. a list -> (a, r) poly -> r =
 fun xs poly ->
  match xs with
  | [] -> ( match poly with Option -> None | Value | Unit -> raise Not_found)
  | x :: _ -> ( match poly with Option -> Some x | Value -> x | Unit -> ())
(*@ r = first xs poly
    ensures match poly with
      | Option -> (match xs with [] -> r === None | x :: _ -> r === Some x)
      | Value -> (match xs with [] -> false | x :: _ -> r === x)
      | Unit -> xs <> []
    raises Not_found -> xs = [] *)

let first_opt (xs : int list) = first xs Option
(*@ r = first_opt xs
    ensures match xs with [] -> r = None | x :: _ -> r = Some x *)

let first_exn (xs : int list) = first xs Value
(*@ r = first_exn xs
    ensures match xs with [] -> false | x :: _ -> r = x
    raises Not_found -> xs = [] *)

let check (xs : int list) = first xs Unit
(*@ check xs
    ensures xs <> []
    raises Not_found -> xs = [] *)
