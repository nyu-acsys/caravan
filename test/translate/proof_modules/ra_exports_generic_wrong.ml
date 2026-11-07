module type INPUT = sig
  (*@ module R : ResourceAlgebra *)
end

module type OUTPUT = sig
  (*@ module Authority : ResourceAlgebra *)
end

module A = struct end
module Make (X : INPUT) : OUTPUT = struct end
module One = Make (A)
