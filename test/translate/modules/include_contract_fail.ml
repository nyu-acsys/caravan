module Original = struct
  let identity (value : int) = value
  (*@ result = identity value ensures result = value *)
end

module Sealed : sig
  val identity : int -> int
  (*@ result = identity value ensures result = 0 *)
end = struct
  include Original
end
