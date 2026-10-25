module Checked : sig
  val identity : int -> int
  (*@ result = identity value ensures result > value *)
end = struct
  let identity (value : int) = value
end
