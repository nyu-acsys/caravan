module type Argument = sig
  type t

  val identity : t -> t
  (*@ result = identity x ensures result === x *)
end

module Integers = struct
  type t = int

  let identity (x : t) = x
  (*@ result = identity x ensures result === x *)
end

module Booleans = struct
  type t = bool

  let identity (x : t) = x
  (*@ result = identity x ensures result === x *)
end

module Outer (X : Argument) = struct
  module Make () = struct
    type t = Value of X.t

    let make x = Value (X.identity x)
    (*@ result = make x ensures result === Value x *)
  end
end

module Integer_scope = Outer (Integers)
module Boolean_scope = Outer (Booleans)
module First = Integer_scope.Make ()
module Second = Integer_scope.Make ()
module Boolean = Boolean_scope.Make ()

let check () =
  match (First.make 7, Second.make 9, Boolean.make true) with
  | First.Value x, Second.Value y, Boolean.Value z -> assert (x = 7 && y = 9 && z)
