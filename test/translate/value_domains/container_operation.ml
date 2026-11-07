module type VALUE = sig
  type t

  val make : unit -> t option list
  (*@ result = make () ensures true *)
end

module Make (Value : VALUE) = struct
  let make () = Value.make ()
  (*@ result = make () ensures true *)
end

module First = Make (Imported_container)
module Again = Make (Imported_container)

let client () =
  let values = First.make () in
  let _ = Again.make () in
  values
