module Make (Cell : sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  val read : t -> int
  (*@ result = read x
      requires counter x state && state >= 0
      ensures counter x state && result >= 0 *)
end) =
struct
  let read x = Cell.read x
  (*@ result = read x
      requires Cell.counter x state && state >= 0
      ensures Cell.counter x state && result >= 0 *)
end

module Left = Make (Actual.First)
module Right = Make (Actual.Second)
module Alias = Left

let read_left x = Alias.read x
(*@ result = read_left x
    requires Actual.First.counter x state && state >= 0
    ensures Actual.First.counter x state && result >= 0 *)

let read_right x = Right.read x
(*@ result = read_right x
    requires Actual.Second.counter x state && state >= 0
    ensures Actual.Second.counter x state && result >= 0 *)
