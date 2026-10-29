module type VIEW = sig
  type t

  (*@ predicate counter (cell : t) (value [@implicit] : int) *)
  val read : t -> int
  (*@ result = read cell requires counter cell value
      ensures counter cell value && result = value *)
end

module Outer (X : VIEW) = struct
  module Make () = struct
    let read cell = X.read cell
    (*@ result = read cell requires X.counter cell value
        ensures X.counter cell value && result = value *)
  end
end

module First = Outer (Actual.First)
module Second = Outer (Actual.Second)
module Left = First.Make ()
module Right = Second.Make ()

let left cell = Left.read cell
(*@ result = left cell requires Actual.First.counter cell value
    ensures Actual.First.counter cell value && result = value *)

let right cell = Right.read cell
(*@ result = right cell requires Actual.Second.counter cell value
    ensures Actual.Second.counter cell value && result = value *)
