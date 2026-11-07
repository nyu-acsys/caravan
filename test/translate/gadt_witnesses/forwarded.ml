(* A witness passed on, to the function itself and to another one, and a raise. *)

type ('a, _) poly = Option : ('a, 'a option) poly | Value : ('a, 'a) poly

let rec last : type a r. a list -> (a, r) poly -> r =
 fun xs poly ->
  match xs with
  | [] -> ( match poly with Option -> None | Value -> raise Not_found)
  | [ x ] -> ( match poly with Option -> Some x | Value -> x)
  | _ :: rest -> last rest poly

let second : type a r. a list -> (a, r) poly -> r =
 fun xs poly -> match xs with [] -> last [] poly | _ :: rest -> last rest poly

let last_opt (xs : int list) = second xs Option
let last_exn (xs : int list) = second xs Value
