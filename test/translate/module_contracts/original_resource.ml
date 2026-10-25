module type View = sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  (*@ predicate ticket (x : t) (n : int) *)
  val read : t -> int

  (*@ result = read x
      requires counter x state && state >= 0 && ticket x 7
      ensures counter x state && ticket x 7 && result >= 0 *)
  val touch : t -> unit
  (*@ touch x requires counter x state ensures counter x state *)
end

module Checked : View = Actual.First

let original x = Actual.First.read x

(*@ result = original x
    requires Actual.First.counter x state
    ensures Actual.First.counter x state && result = state *)
let checked x = Checked.read x
(*@ result = checked x
    requires Checked.counter x state && state >= 0 && Checked.ticket x 7
    ensures Checked.counter x state && Checked.ticket x 7 && result >= 0 *)
