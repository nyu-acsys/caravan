type t = int

module Scoped : sig
  type t

  val identity : int -> int
  (*@ result = identity value ensures forall witness : t. witness = witness *)
end = struct
  let identity (value : int) = value

  type t = bool
end
