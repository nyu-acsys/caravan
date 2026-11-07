module Scoped : sig
  val helper : int -> bool
  val identity : int -> int
  (*@ result = identity value ensures helper value *)
end = struct
  let helper (_value : int) = true
  let helper (_value : int) = false
  let identity (value : int) = value
end
