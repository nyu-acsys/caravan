module type CELL = sig
  type t

  (*@ predicate counter (cell : t) (n [@implicit] : int) *)
  val read : t -> int
  (*@ result = read cell
      requires counter cell n
      ensures counter cell n && result = n *)
end

module Make (Cell : CELL) = struct
  type t = Cell.t

  let read (cell : Cell.t) = Cell.read cell
  (*@ Ghost.scope (fun step ->
      fold wrapped cell;
      preserve cell;
      unfold wrapped cell;
      let result = step () in
      result) *)
  (*@ manual *)
  (*@ result = read cell
      requires Cell.counter cell n
      ensures Cell.counter cell n && result = n
        && is_empty (singleton cell) = false *)
end

module First = Make (Actual.First)
module Second = Make (Actual.Second)
module Alias = First
module Repeated = Make (Actual.First)

module Sealed : sig
  type t = First.t
end =
  First

let read_first (cell : First.t) = Alias.read cell
(*@ result = read_first cell
    requires Actual.First.counter cell n
    ensures Actual.First.counter cell n && result = n
      && First.is_empty (First.singleton cell) = false *)
