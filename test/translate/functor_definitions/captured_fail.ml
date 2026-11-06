module type Value = sig
  type t

  val identity : t -> t
  (*@ result = identity x ensures result === x *)
end

module Outer (X : Value) = struct
  module Inner () = struct
    let incorrect (x : X.t) = X.identity x
    (*@ result = incorrect x ensures false *)
  end
end
