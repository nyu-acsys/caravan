module type IMPOSSIBLE = sig
  val id : 'a -> 'a
  (*@ result = id value ensures false *)
end

module Apply (Argument : IMPOSSIBLE) = struct
  let id value = Argument.id value
end

module Rejected = Apply (Argument)
