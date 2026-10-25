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

module Left : sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  (*@ predicate ticket (x : t) (n : int) *)
  val read : t -> int

  (*@ result = read x requires counter x state && state >= 0 && ticket x 7
      ensures counter x state && ticket x 7 && result >= 0 *)
  val touch : t -> unit
  (*@ touch x requires counter x state ensures counter x state *)
end =
  Actual.First

module Right : View = Actual.Second
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
