module type View = sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  (*@ predicate ticket (x : t) (n : int) *)
  val read : t -> int

  (*@ result = atomic read x
      requires ticket x 7
      ensures ticket x 7
      atomic requires counter x state && state >= 0
      atomic ensures counter x state && result >= 0 *)
  val touch : t -> unit
  (*@ atomic touch x atomic requires counter x state atomic ensures counter x state *)
end

module Checked : View = Actual.Atomic_first

let client x =
  let result = Checked.read x in
  assert (result = 7)
(*@ client x requires Checked.counter x 7 && Checked.ticket x 7 *)
