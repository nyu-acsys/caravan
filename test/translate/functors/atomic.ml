module type View = sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  val read : t -> int

  (*@ result = atomic read x
      atomic requires counter x state && state >= 0
      atomic ensures counter x state && result >= 0 *)
  val touch : t -> unit
  (*@ atomic touch x atomic requires counter x state atomic ensures counter x state *)
end

module Make (Cell : View) = struct
  let read x = Cell.read x
  (*@ result = read x
      requires Cell.counter x state && state >= 0
      ensures Cell.counter x state && result >= 0 *)

  let touch x = Cell.touch x
  (*@ touch x requires Cell.counter x state ensures Cell.counter x state *)
end

module Left = Make (Actual.Atomic_first)
module Right = Make (Actual.Atomic_second)

let read x = Left.read x
(*@ result = read x
    requires Actual.Atomic_first.counter x state && state >= 0
    ensures Actual.Atomic_first.counter x state && result >= 0 *)

let touch x = Right.touch x
(*@ touch x requires Actual.Atomic_second.counter x state ensures Actual.Atomic_second.counter x state *)
