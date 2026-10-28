module type VIEW = sig
  (*@ module R : ResourceAlgebra *)
  (*@ module R : ResourceAlgebra *)
end

module A = struct end

module Make (X : VIEW) = struct
  let mark (value : int) = value
end

module One = Make (A)
