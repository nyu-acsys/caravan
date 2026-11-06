module type Value = sig
  type t
end

module Make (X : Value) = struct
  let identity (x : X.t) = x
  (*@ result = identity x ensures result === x *)
end
