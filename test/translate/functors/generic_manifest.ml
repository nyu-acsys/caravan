module type View = sig
  type t = Actual.First.t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  val read : t -> int
  (*@ result = read x requires counter x state ensures counter x state && result = state *)
end

module Make (Cell : View) = struct
  let read (x : Cell.t) = Cell.read x
  (*@ result = read x requires Cell.counter x state ensures Cell.counter x state && result = state *)
end

module First = Make (Actual.First)
module Repeated = Make (Actual.First)

let client x =
  let first = First.read x in
  let second = Repeated.read x in
  assert (first = second);
  second
(*@ result = client x requires Actual.First.counter x state ensures Actual.First.counter x state && result = state *)
