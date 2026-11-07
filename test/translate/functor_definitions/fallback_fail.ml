module type Argument = sig
  type t = A | B
end

module Unit () = struct
  let identity (x : int) = x
end

module Make (X : Argument) = struct
  module Instance = Unit ()

  let check () = assert false
end
