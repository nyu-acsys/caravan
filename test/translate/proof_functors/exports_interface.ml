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

  let read (cell : t) = Cell.read cell
  (*@ Ghost.scope (fun step ->
      fold wrapped cell { same = cell };
      preserve cell;
      let same = unfold wrapped cell { same } in
      assert (same === cell);
      let result = step () in
      result) *)
  (*@ manual *)
  (*@ result = read cell
      requires Cell.counter cell n
      ensures Cell.counter cell n && result = n *)
end

module Open = Make (Actual.First)

module Sealed : sig
  type t
  (*@ predicate wrapped (cell : t) (n [@implicit] : int) *)
end =
  Make (Actual.First)

module Alias = Sealed
