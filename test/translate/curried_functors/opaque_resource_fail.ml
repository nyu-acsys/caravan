module type Cell = sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  val read : t -> int
  (*@ result = read x requires counter x state ensures counter x state && result = state *)
end

module Left : Cell = Actual.First
module Right : Cell = Actual.First

module Make (X : sig
  type t
end) (Y : sig
  (*@ predicate counter (x : X.t) (n [@implicit] : int) *)
end) =
struct end

module Partial = Make (Left)
module Incorrect = Partial (Right)
