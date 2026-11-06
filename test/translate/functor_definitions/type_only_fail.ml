module type Value = sig
  type t
end

module Make (X : Value) = struct
  type t = X.t
end
