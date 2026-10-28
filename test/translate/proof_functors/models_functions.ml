module type CELL = sig
  type t
end

module Make (Cell : CELL) = struct
  let identity (cell : Cell.t) = cell
end

module First = Make (Actual.First)
module Second = Make (Actual.Second)
module Alias = First
