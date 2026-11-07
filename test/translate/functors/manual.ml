module type View = sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  val read : t -> int
  (*@ result = read x requires counter x state ensures counter x state && result = state *)
end

module Make (Cell : View) = struct
  let read x = Cell.read x
  (*@ Ghost.scope (fun invoke -> let result = invoke () in result) *)
  (*@ manual *)
  (*@ result = read x requires Cell.counter x state ensures Cell.counter x state && result = state *)
end

module Left = Make (Actual.First)
module Right = Make (Actual.Second)

let read_left x = Left.read x
(*@ result = read_left x
    requires Actual.First.counter x state
    ensures Actual.First.counter x state && result = state *)

let read_right x = Right.read x
(*@ result = read_right x
    requires Actual.Second.counter x state
    ensures Actual.Second.counter x state && result = state *)
