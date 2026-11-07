module Nested : sig
  type t

  (*@ invariant zero (x : t) *)

  val read : t -> int
  (*@ result = read x requires zero x ensures zero x && result = 0 *)
end
