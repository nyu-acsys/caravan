module Sealed : sig
  type t

  val make : int -> t
end = struct
  type t = int

  let make (value : int) = value
end

let client (value : Sealed.t) = ()
(*@ client value requires Contract_api.number value *)
