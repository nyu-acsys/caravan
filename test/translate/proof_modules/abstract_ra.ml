module type VIEW = sig
  (*@ module R : ResourceAlgebra *)
end

module A = struct end
module B = struct end

module Make (X : VIEW) = struct
  let mark (value : int) = value
  (*@ result = mark value
      ensures result = value
      ensures (X.R.valid X.R.id) *)
end

module One = Make (A)
module Two = Make (B)

let one (value : int) = One.mark value
(*@ result = one value ensures result = value *)

let two (value : int) = Two.mark value
(*@ result = two value ensures result = value *)
