module type View = sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  val read : t -> int
  (*@ result = read x requires counter x state ensures counter x state && result = state *)
end

module Make (Cell : View) = struct
  type t = Cell.t

  let read (x : t) = Cell.read x
  (*@ result = read x requires Cell.counter x state ensures Cell.counter x state && result = state *)
end

module Left = Make (Actual.First)
module Right = Make (Actual.Second)

let read (x : Left.t) = Left.read x
(*@ result = read x
    requires Actual.First.counter x state
    ensures Actual.First.counter x state && result = state *)
