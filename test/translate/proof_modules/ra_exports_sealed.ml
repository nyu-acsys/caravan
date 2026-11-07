module type VIEW = sig
  (*@ module R : ResourceAlgebra *)
end

module A : VIEW = struct end
module B : VIEW = struct end
module Alias = A

let marker (value : int) = value
(*@ result = marker value ensures result = value *)
