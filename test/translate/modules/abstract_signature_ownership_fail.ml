module Sealed : sig
  type t

  val identity : t -> t
  (*@ result = identity cell requires own cell 0 ensures own result 0 *)
end = struct
  type t = int Atomic.t

  let identity (cell : t) = cell
end
