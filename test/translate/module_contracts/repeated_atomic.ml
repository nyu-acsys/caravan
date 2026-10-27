module type View = sig
  type t = Actual.Atomic_first.t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  val read : t -> int

  (*@ result = atomic read x
      atomic requires counter x state && state >= 0
      atomic ensures counter x state && result >= 0 *)
  val touch : t -> unit
  (*@ atomic touch x atomic requires counter x state atomic ensures counter x state *)
end

module Actual_alias = Actual.Atomic_first
module Original : View = Actual.Atomic_first
module Repeated : View = Actual.Atomic_first
module Via_actual_alias : View = Actual_alias
module Original_alias = Original
module Checked : View = Original_alias
module Checked_again : View = Checked

let client x =
  let first = Original.read x in
  let second = Repeated.read x in
  let third = Via_actual_alias.read x in
  let fourth = Checked.read x in
  let fifth = Checked_again.read x in
  Checked_again.touch x;
  assert (first >= 0 && second >= 0 && third >= 0 && fourth >= 0 && fifth >= 0)
(*@ client x
    requires Original.counter x state && state >= 0
    ensures Checked_again.counter x state *)
