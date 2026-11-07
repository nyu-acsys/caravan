module type View = sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  val read : t -> int
  (*@ result = read x requires counter x state ensures counter x state && result = state *)
end

module Make (Cell : View) = struct
  let read (x : Cell.t) =
    let box = ref x in
    Cell.read !box
  (*@ result = read x requires Cell.counter x state ensures Cell.counter x state && result = state *)
end

module First = Make (Actual.First)
module Second = Make (Actual.Second)

let first x = First.read x
(*@ result = first x requires Actual.First.counter x state ensures Actual.First.counter x state && result = state *)

let second x = Second.read x
(*@ result = second x requires Actual.Second.counter x state ensures Actual.Second.counter x state && result = state *)
