module type Value = sig
  val identity : int -> int
  (*@ result = identity x ensures result = x *)
end

module Wrong = struct
  let identity (x : int) = 0
  (*@ result = identity x ensures result = 0 *)
end

module Make (X : Value) (Y : Value) = struct
  let identity (x : int) = X.identity (Y.identity x)
  (*@ result = identity x ensures result = x *)
end

module Partial = Make (Wrong)
