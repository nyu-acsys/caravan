module type INPUT = sig
  (*@ module R : ResourceAlgebra *)
end

module A = struct end

module Make (X : INPUT) = struct
  let marker (value : int) = value
  (*@ result = marker value ensures result = value *)
end

module One = Make (A)

let use (value : int) = One.marker value
(*@ result = use value ensures result = value *)
