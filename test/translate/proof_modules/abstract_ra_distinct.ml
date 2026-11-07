module type VIEW = sig
  (*@ module Left : ResourceAlgebra *)
  (*@ module Right : ResourceAlgebra *)
end

module A = struct end

module Make (X : VIEW) = struct
  let mark (value : int) = value
end

module One = Make (A)
