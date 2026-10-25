module Sealed : sig
  type t

  val identity : t -> t
  (*@ result = identity value requires length value = 0 ensures result = value *)
end = struct
  type t = int list

  let identity (value : t) = value
end
