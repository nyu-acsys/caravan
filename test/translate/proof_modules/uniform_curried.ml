module type INPUT = sig
  (*@ module R : ResourceAlgebra *)
  (*@ predicate token (cell : Ghost.t) (value : R.t) *)
end

module A = struct end
module B = struct end

module Make (X : INPUT) (Y : INPUT) = struct
  let marker (value : int) = value
  (*@ result = marker value
      requires X.token left X.R.id && Y.token right Y.R.id
      ensures X.token left X.R.id && Y.token right Y.R.id && result = value *)
end

module Direct = Make (A) (B)
module Partial = Make (A)
module Applied = Partial (B)
module Alias = Direct
module PartialAlias = Partial
module ViaAlias = PartialAlias (B)
module Swapped = Make (B) (A)
module Hidden : sig end = Make (A) (B)
