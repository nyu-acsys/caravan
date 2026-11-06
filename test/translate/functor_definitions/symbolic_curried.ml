module type Value = sig
  type t

  val identity : t -> t
  (*@ result = identity x ensures result === x *)
end

module Pair (X : Value) (Y : Value) = struct
  let first (x : X.t) = X.identity x

  (*@ result = first x ensures result === x *)
  let second (y : Y.t) = Y.identity y
  (*@ result = second y ensures result === y *)
end

module Outer (X : Value) = struct
  module Partial = Pair (X)
  module Result = Partial (X)

  let identity (x : X.t) = Result.first (Result.second x)
  (*@ result = identity x ensures result === x *)
end
