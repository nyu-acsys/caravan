module type View = sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  val read : t -> int
  (*@ result = read x requires counter x state ensures counter x state && result = state *)
end

module Helper = struct
  let identity (x : int) = x
  (*@ result = identity x ensures result = x *)
end

let identity (x : int) = x
(*@ result = identity x ensures result = x *)

module Make (Cell : View) = struct
  let read x = identity (Helper.identity (Cell.read x))
  (*@ result = read x requires Cell.counter x state ensures Cell.counter x state && result = state *)
end

module Scope = struct
  module Helper = struct
    let identity (_x : int) = 0
    (*@ result = identity _x ensures result = 0 *)
  end

  let identity (_x : int) = 0
  (*@ result = identity _x ensures result = 0 *)

  module Left = Make (Actual.First)
  module Right = Make (Actual.First)
end

let read_left x = Scope.Left.read x
(*@ result = read_left x
    requires Actual.First.counter x state
    ensures Actual.First.counter x state && result = state *)

let read_right x = Scope.Right.read x
(*@ result = read_right x
    requires Actual.First.counter x state
    ensures Actual.First.counter x state && result = state *)
