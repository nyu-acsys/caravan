module type VIEW = sig
  (*@ module R : ResourceAlgebra *)
end

module A = struct end

module Make (X : VIEW) = struct
  let mark (value : int) = value
  (*@ result = mark value
      ensures result = value
      ensures (X.R.valid X.R.id) *)
end

module One = Make (A)
