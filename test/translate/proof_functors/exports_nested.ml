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

module Outer : sig
  module Exported : sig
    type t = Actual.First.t
    (*@ predicate wrapped (cell : t) (n [@implicit] : int) *)
  end
end = struct
  module Exported = Make (Actual.First)

  let internal (cell : Exported.t) = Exported.read cell
  (*@ Ghost.scope (fun step ->
      fold Exported.wrapped cell { same = cell };
      Exported.preserve cell;
      let same = unfold Exported.wrapped cell { same } in
      assert (same === cell);
      let result = step () in
      result) *)
  (*@ manual *)
  (*@ result = internal cell
      requires Actual.First.counter cell n
      ensures Actual.First.counter cell n && result = n *)
end
