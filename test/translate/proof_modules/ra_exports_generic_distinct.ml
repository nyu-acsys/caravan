module type INPUT = sig
  (*@ module R : ResourceAlgebra *)
end

module type OUTPUT = sig
  (*@ module Authority : ResourceAlgebra *)
  val marker : unit -> unit
end

module A = struct end
module B = struct end

module Make (X : INPUT) : OUTPUT = struct
  let marker () = ()
end

module One = Make (A)
module Two = Make (B)
