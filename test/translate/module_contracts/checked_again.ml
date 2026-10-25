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

module Original : View = Actual.First
module Checked : View = Original
module Alias = Checked

let client x = Alias.read x
(*@ result = client x
    requires Checked.counter x state && state >= 0 && Checked.ticket x 7
    ensures Alias.counter x state && Alias.ticket x 7 && result >= 0 *)
