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

module Outer = struct
  module Checked : View = Actual.First

  module Nested = struct
    module Alias = Checked

    let read x = Alias.read x
    (*@ result = read x
        requires Checked.counter x state && state >= 0 && Checked.ticket x 7
        ensures Alias.counter x state && Alias.ticket x 7 && result >= 0 *)
  end
end

let client x = Outer.Nested.read x
(*@ result = client x
    requires Outer.Checked.counter x state && state >= 0 && Outer.Checked.ticket x 7
    ensures Outer.Checked.counter x state && Outer.Checked.ticket x 7 && result >= 0 *)
