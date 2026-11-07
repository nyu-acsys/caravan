module Sealed : sig
  val value : unit -> int
end = struct
  let value () = 7
end

let client () = 0
(*@ result = client () ensures Sealed.value () = 7 *)
