(*@ module R : ResourceAlgebra *)
(*@ predicate direct_token (cell : Ghost.t) (value : R.t) *)

val direct_keep : unit -> unit
(*@ direct_keep ()
    requires direct_token cell R.id
    ensures direct_token cell R.id *)

module Nested : sig
  (*@ module R : ResourceAlgebra *)
end

module type VIEW = sig
  (*@ module R : ResourceAlgebra *)
  (*@ predicate token (cell : Ghost.t) (value : R.t) *)

  val keep : unit -> unit
  (*@ keep () requires token cell value ensures token cell value *)
end
