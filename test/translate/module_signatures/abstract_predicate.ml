module Sealed : sig
  type t

  val identity : t -> t
  (*@ result = identity value
      requires Contract_api.number value
      ensures Contract_api.number result *)
end = struct
  type t = int

  let identity (value : int) = value
end
