module type Value = sig
  type t

  val identity : t -> t
  (*@ result = identity x ensures result === x *)
end

module Make (X : Value) = struct
  module Alias = X

  let identity (x : Alias.t) = Alias.identity x
  (*@ result = identity x ensures result === x *)
end
