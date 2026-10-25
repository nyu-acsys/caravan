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

let client (x : Checked.t) = Checked.read x
(*@ result = client x
    requires Actual.First.counter x state && state >= 0 && Checked.ticket x 7
    ensures Checked.counter x state && Checked.ticket x 7 && result >= 0 *)
