module type VIEW = sig
  (*@ module R : ResourceAlgebra *)
  (*@ predicate token (cell : Ghost.t) (value : R.t) *)

  val keep : unit -> unit
  (*@ keep () requires token cell value ensures token cell value *)
end

module A : VIEW = struct
  let keep () = ()
end

module Alias = A
