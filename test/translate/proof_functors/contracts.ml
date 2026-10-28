module type CELL = sig
  type t

  (*@ predicate counter (cell : t) (n [@implicit] : int) *)
  val read : t -> int
  (*@ result = read cell
      requires counter cell n
      ensures counter cell n && result = n *)
end

module Make (Cell : CELL) = struct
  let helper (cell : Cell.t) = Cell.read cell
  (*@ Ghost.scope (fun step ->
      unfold wrapped cell;
      let result = step () in
      fold wrapped cell;
      result) *)
  (*@ manual *)
  (*@ result = helper cell
      requires wrapped cell n
      ensures wrapped cell n && result = n *)

  let read (cell : Cell.t) = helper cell
  (*@ Ghost.scope (fun step ->
      fold wrapped cell;
      preserve cell;
      let result = step () in
      unfold wrapped cell;
      result) *)
  (*@ manual *)
  (*@ result = read cell
      requires Cell.counter cell n
      ensures Cell.counter cell n && result = n *)
end

module First = Make (Actual.First)
module Second = Make (Actual.Second)
module Alias = First

let read_first (cell : Actual.First.t) = Alias.read cell
(*@ result = read_first cell
    requires Actual.First.counter cell n
    ensures Actual.First.counter cell n && result = n *)

let read_second (cell : Actual.Second.t) = Second.read cell
(*@ result = read_second cell
    requires Actual.Second.counter cell n
    ensures Actual.Second.counter cell n && result = n *)
