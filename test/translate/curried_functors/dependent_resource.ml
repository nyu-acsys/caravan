module type Value = sig
  type t
end

module Make
    (X : Value)
    (Cell : sig
      (*@ predicate counter (x : X.t) (n [@implicit] : int) *)
      val read : X.t -> int
      (*@ result = read x requires counter x state ensures counter x state && result = state *)
    end) =
struct
  let read (x : X.t) = Cell.read x
  (*@ result = read x requires Cell.counter x state ensures Cell.counter x state && result = state *)
end

module With_cell = Make (Actual.First)
module Instance = With_cell (Actual.First)

let read x = Instance.read x
(*@ result = read x requires Actual.First.counter x state ensures Actual.First.counter x state && result = state *)

module type Cell = sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  val read : t -> int
  (*@ result = read x requires counter x state ensures counter x state && result = state *)
end

module Outer (Cell : Cell) = struct
  module Partial = Make (Cell)
  module Result = Partial (Cell)

  let read (x : Cell.t) = Result.read x
  (*@ result = read x requires Cell.counter x state ensures Cell.counter x state && result = state *)
end

module Nested = Outer (Actual.First)

let nested_read x = Nested.read x
(*@ result = nested_read x requires Actual.First.counter x state ensures Actual.First.counter x state && result = state *)
