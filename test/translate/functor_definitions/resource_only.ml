module type Value = sig
  type t
end

module Make
    (X : Value)
    (Resource : sig
      (*@ predicate owned (x : X.t) *)
    end) =
struct
  let identity (x : X.t) = x
  (*@ result = identity x
      requires Resource.owned x
      ensures Resource.owned x && result === x *)
end
