module type View = sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  (*@ predicate missing (x : t) (n : int) *)
  val read : t -> int

  (*@ result = read x requires counter x n ensures counter x n && result = n *)
  val touch : t -> unit
  (*@ touch x requires counter x n ensures counter x n *)
end

module Checked : View = Actual.First
