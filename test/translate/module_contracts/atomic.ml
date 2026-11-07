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

module Left : View = Actual.Atomic_first
module Right : View = Actual.Atomic_second
module Alias = Left

let read_left x = Alias.read x

(*@ result = read_left x
    requires Left.counter x state && state >= 0 && Left.ticket x 7
    ensures Alias.counter x state && Alias.ticket x 7 && result >= 0 *)
let read_right x = Right.read x

(*@ result = read_right x
    requires Right.counter x state && state >= 0 && Right.ticket x 7
    ensures Right.counter x state && Right.ticket x 7 && result >= 0 *)
let touch x = Alias.touch x
(*@ touch x requires Left.counter x state ensures Alias.counter x state *)
