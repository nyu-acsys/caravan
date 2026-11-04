(* Functions whose result type a witness selects, called with each witness. *)

type ('a, _) poly =
  | Option : ('a, 'a option) poly
  | Value : ('a, 'a) poly
  | Unit : ('a, unit) poly

let first : type a r. a list -> a -> (a, r) poly -> r =
 fun xs default poly ->
  match xs with
  | [] -> ( match poly with Option -> None | Value -> default | Unit -> ())
  | x :: _ -> ( match poly with Option -> Some x | Value -> x | Unit -> ())

let first_opt (xs : int list) = first xs 0 Option
let first_value (xs : int list) = first xs 0 Value
let first_unit (xs : bool list) = first xs true Unit

(* At a type parameter of the caller. *)
let first_or xs default = first xs default Value

(* A match on the witness whose value is not of the selected type. *)
let wraps : type a r. (a, r) poly -> bool =
 fun poly -> match poly with Option -> true | Value | Unit -> false

let wraps_int () = wraps (Option : (int, int option) poly)
