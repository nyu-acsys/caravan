module Sealed : sig
  val identity : int -> int
end = struct
  let identity (value : int) = value
  (*@ result = identity value ensures result = value *)
end

let client value = Sealed.identity value
(*@ result = client value ensures result = value *)
