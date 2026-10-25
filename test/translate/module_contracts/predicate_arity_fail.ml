module type View = sig
  type t

  (*@ predicate counter (x : t) (extra : int) (n [@implicit] : int) *)
  (*@ predicate ticket (x : t) (n : int) *)
  val read : t -> int

  (*@ result = read x requires counter x 0 n ensures counter x 0 n && result = n *)
  val touch : t -> unit
  (*@ touch x requires counter x 0 n ensures counter x 0 n *)
end

module Checked : View = Actual.First
