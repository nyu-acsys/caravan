module Sealed : sig
  type t

  val make : int -> t
end = struct
  type t = int

  let make (value : int) = value
end

let singleton value = Some (Sealed.make value)
(*@ result = singleton value
    ensures match result with Some hidden -> hidden + 1 = value | None -> true *)
