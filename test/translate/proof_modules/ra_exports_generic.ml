module type INPUT = sig
  (*@ module R : ResourceAlgebra *)
end

module type OUTPUT = sig
  (*@ module Authority : ResourceAlgebra *)
  val marker : int -> int
  (*@ result = marker value ensures result = value *)
end

module A = struct end
module B = struct end

module Make (X : INPUT) : OUTPUT = struct
  let marker (value : int) = value
end

module One = Make (A)
module Two = Make (B)
module Again = Make (A)
module Alias = One
module F = Make
module ArgAlias = A
module Aliased = F (ArgAlias)

let use_one (value : int) = One.marker value
(*@ result = use_one value ensures result = value *)

let use_two (value : int) = Two.marker value
(*@ result = use_two value ensures result = value *)
