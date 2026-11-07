module type CELL = sig
  type t
end

module Static = struct
  type t = int
end

module Make (Cell : CELL) = struct
  type t = Cell.t
end
