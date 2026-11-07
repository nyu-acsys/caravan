module type View = sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  (*@ predicate ticket (x : t) (n : int) *)
  val read : t -> int

  (*@ result = atomic read x atomic requires counter x n atomic ensures counter x n && result = n + 1 *)
  val touch : t -> unit
  (*@ atomic touch x atomic requires counter x n atomic ensures counter x n *)
end

module Checked : View = Actual.Atomic_first
