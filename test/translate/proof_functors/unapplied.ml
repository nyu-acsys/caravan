module type CELL = sig
  type t
end

module Make (Cell : CELL) = struct
  let identity (cell : Cell.t) = cell
end
