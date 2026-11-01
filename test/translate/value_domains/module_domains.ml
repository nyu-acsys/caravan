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
