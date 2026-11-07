module type VALUE = sig
  type t

  val make : unit -> t
  (*@ result = make () ensures true *)
end

module Make (Value : VALUE) = struct
  let make () = Value.make ()
  (*@ result = make () ensures true *)

  let identity (values : Value.t list) = values
  (*@ result = identity values ensures result === values *)

  let nested (values : Value.t option list list) = values
  (*@ result = nested values ensures result === values *)

  let pair (value : Value.t * Value.t option list * bool) = value
  (*@ result = pair value ensures result === value *)

  let pack (value : Value.t) (flags : bool list) = (value, flags)
  (*@ result = pack value flags ensures result === (value, flags) *)

  let head (values : Value.t option list) =
    match values with [] -> None | value :: _ -> value
  (*@ result = head values ensures
      match values with [] -> result === None | value :: _ -> result === value *)

  let tail (values : Value.t option list) =
    match values with [] -> [] | _ :: tail -> tail
  (*@ result = tail values ensures
      match values with [] -> result === [] | _ :: tail -> result === tail *)
end

module First = Make (Imported_values)
module Again = Make (Imported_values)
module Second = Make (Imported_other)

let first () = First.make ()
let repeated () = Again.make ()
let second () = Second.make ()
let first_list (values : Imported_values.t list) = First.identity values
(*@ result = first_list values ensures result === values *)

let second_list (values : Imported_other.t list) = Second.identity values
(*@ result = second_list values ensures result === values *)

let nested (values : Imported_values.t option list list) = Again.nested values
(*@ result = nested values ensures result === values *)

let pair (value : Imported_values.t * Imported_values.t option list * bool) =
  First.pair value
(*@ result = pair value ensures result === value *)

let head (values : Imported_values.t option list) = First.head values
(*@ result = head values ensures
    match values with [] -> result === None | value :: _ -> result === value *)

let tail (values : Imported_values.t option list) = Again.tail values
(*@ result = tail values ensures
    match values with [] -> result === [] | _ :: tail -> result === tail *)

let pack (value : Imported_values.t) (flags : bool list) = First.pack value flags
(*@ result = pack value flags ensures result === (value, flags) *)
