module type Value = sig
  type t

  val identity : t -> t
  (*@ result = identity x ensures result === x *)
end

module Make (X : Value) = struct
  let identity (x : X.t) = X.identity x
  (*@ result = identity x ensures result === x *)
end

module Curried (X : Value) () (Y : Value) = struct
  let first (x : X.t) = X.identity x
  (*@ result = first x ensures result === x *)

  let second (y : Y.t) = Y.identity y
  (*@ result = second y ensures result === y *)
end

module Scope = struct
  module Make (X : Value) = struct
    let identity (x : X.t) = X.identity x
    (*@ result = identity x ensures result === x *)
  end
end

module Unit () = struct
  let identity (x : int) = x
  (*@ result = identity x ensures result = x *)
end
